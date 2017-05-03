//===-- LocalExecutor.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "LocalExecutor.h"
#include "Context.h"
#include "CoreStats.h"
#include "ExternalDispatcher.h"
#include "ImpliedValue.h"
#include "MemoryManager.h"
#include "PTree.h"
#include "Searcher.h"
#include "SeedInfo.h"
#include "SpecialFunctionHandler.h"
#include "StatsTracker.h"
#include "TimingSolver.h"
#include "UserSearcher.h"
#include "ExecutorTimerInfo.h"

#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Interpreter.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/CommandLine.h"
#include "klee/Common.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprSMTLIBPrinter.h"
#include "klee/util/ExprUtil.h"
#include "klee/util/GetElementPtrTypeIterator.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/FloatEvaluation.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/System/MemoryUsage.h"
#include "klee/SolverStats.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/TypeBuilder.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#include <iostream>

using namespace llvm;

namespace klee {
  
cl::opt<bool>
AssumeInboundPointers("assume-inbound-pointers",
                      cl::init(true),
                      cl::desc("Assume pointer dereferences are inbounds. (default=on)"));
  
LocalExecutor::LocalExecutor(LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih,
                             const std::set<std::string> &fns) :
Executor(ctx, opts, ih),
lazyAllocationCount(16),
fnInModule(fns)
{
    
}

LocalExecutor::~LocalExecutor() {
    
    
}

#ifdef NEVER
uint64_t LocalExecutor::getAddr(ExecutionState& state, ref<Expr> addr) const {

  uint64_t result = 0;

  if (isa<ConstantExpr>(addr)) {
    ref<ConstantExpr> caddr = cast<ConstantExpr>(addr);
    result = caddr->getZExtValue();
  } else {

    ref<ConstantExpr> cex;
    if (solver->getValue(state, addr, cex)) {
      result = cex->getZExtValue();
    }
  }
  return result;
}

int64_t LocalExecutor::getValue(ExecutionState& state, ref<Expr> value) const {

  int64_t result = 0;

  if (isa<ConstantExpr>(value)) {
    ref<ConstantExpr> cvalue = cast<ConstantExpr>(value);
    result = cvalue->getAPValue().getSExtValue();
  } else {

    ref<ConstantExpr> cex;
    if (solver->getValue(state, value, cex)) {
      result = cex->getAPValue().getSExtValue();
    }
  }
  return result;
}
#endif

bool LocalExecutor::resolveMO(ExecutionState &state, ref<Expr> address, ObjectPair &op) {

  bool result = false;

  assert(address.get()->getWidth() == Context::get().getPointerWidth());

  if (isa<ConstantExpr>(address)) {
    ref<ConstantExpr> caddress = cast<ConstantExpr>(address);

    // fast path: single in-bounds resolution
    result = state.addressSpace.resolveOne(caddress, op);
  }
  if (!result) {

    // not a const address, so we have to ask the solver
    solver->setTimeout(coreSolverTimeout);
    if (!state.addressSpace.resolveOne(state, solver, address, true, op, result)) {
      address = toConstant(state, address, "resolveOne failure");
      result = state.addressSpace.resolveOne(cast<ConstantExpr>(address), op);
    }
    solver->setTimeout(0);
  }
  return result;
}


bool LocalExecutor::isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e) {

  bool result = false;
  if (e->getWidth() == Context::get().getPointerWidth()) {
    solver->setTimeout(coreSolverTimeout);
    auto range = solver->getRange(state, e);
    solver->setTimeout(0);
    ref<Expr> low = range.first;
    ref<Expr> high = range.second;
    
    if (low->getKind() == Expr::Kind::Constant && high->getKind() == Expr::Kind::Constant) {
      
      uint64_t clow = cast<ConstantExpr>(low)->getZExtValue();
      uint64_t chigh = cast<ConstantExpr>(high)->getZExtValue();
      result = ((clow == 0) && (chigh == UINT64_MAX));
    }
  }
  return result;
}
  
bool LocalExecutor::executeReadMemoryOperation(ExecutionState &state,
                                               ref<Expr> address,
                                               const Type *type,
                                               KInstruction *target) {

  ObjectPair op;
  if (!resolveMO(state, address, op)) {
    return false;
  }

  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  Expr::Width width = getWidthForLLVMType(target->inst->getType());
  unsigned bytes = Expr::getMinBytesForWidth(width);

  ref<Expr> offsetExpr = mo->getOffsetExpr(address);
  if (isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> coffsetExpr = cast<ConstantExpr>(offsetExpr);
    const unsigned offset = (unsigned) coffsetExpr->getZExtValue();
    if (offset + bytes > mo->size) {
      terminateStateOnError(state, "memory error: out of bound pointer", Ptr,
                            NULL, getAddressInfo(state, address));
      return false;
    }
  } else {

    solver->setTimeout(coreSolverTimeout);
    ref<Expr> mc = mo->getBoundsCheckOffset(offsetExpr, bytes);

    if (AssumeInboundPointers) {
      bool inBounds;
      if (!solver->mayBeTrue(state, mc, inBounds) || !inBounds) {
        solver->setTimeout(0);
        state.pc = state.prevPC;
        terminateStateEarly(state, "Failed to resolve read memory offset.");
      }
      addConstraint(state, mc);

    } else {
      klee_error("non-optimistic not supported at this time");
    }
    solver->setTimeout(0);
  }

  if (!state.isSymbolic(mo) && !isLocallyAllocated(state, mo)) {
    os = makeSymbolic(state, mo, os);
  }
  
  ref<Expr> e = os->read(offsetExpr, width);
  if ((countLoadIndirection(type) > 1) && (isUnconstrainedPtr(state, e))) {
    // this is an unconstrained ptr-ptr. allocate something behind the pointer

    Type *subtype = type->getPointerElementType()->getPointerElementType();
    MemoryObject *newMO = allocMemory(state, subtype, target->inst, MemKind::lazy,
                                      '*' + mo->name, 0, lazyAllocationCount);
    bindObjectInState(state, newMO);
    
    // and constrain this pointer to point at it.
    ref<ConstantExpr> ptr = newMO->getBaseExpr();
    ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(e, ptr));
    state.addConstraint(eq);
  }
  bindLocal(target, state, e);
  return true;
}
  
bool LocalExecutor::executeWriteMemoryOperation(ExecutionState &state,
                                                ref<Expr> address,
                                                ref<Expr> value,
                                                const std::string name) {

  ObjectPair op;
  if (!resolveMO(state, address, op)) {
    return false;
  }

  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  if (os->readOnly) {
    terminateStateOnError(state, "memory error: object read only", ReadOnly);
  }

  Expr::Width width = value->getWidth();
  unsigned bytes = Expr::getMinBytesForWidth(width);

  // propagate address name, if unset
  if ((mo->name.empty()) && (!name.empty())) {
    mo->name = name;
  }

  ref<Expr> offsetExpr = mo->getOffsetExpr(address);
  if (isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> coffsetExpr = cast<ConstantExpr>(offsetExpr);
    const unsigned offset = (unsigned) coffsetExpr->getZExtValue();
    if (offset + bytes > mo->size) {

      terminateStateOnError(state, "memory error: out of bound pointer", Ptr,
                            NULL, getAddressInfo(state, address));
      return false;
    }
  } else {

    solver->setTimeout(coreSolverTimeout);
    ref<Expr> mc = mo->getBoundsCheckOffset(offsetExpr, bytes);

    if (AssumeInboundPointers) {
      bool inBounds;
      if (!solver->mayBeTrue(state, mc, inBounds) || !inBounds) {
        solver->setTimeout(0);
        state.pc = state.prevPC;
        terminateStateEarly(state, "Failed to resolve write memory offset.");
      }
      addConstraint(state, mc);

    } else {
      klee_error("non-optimistic not supported at this time");
    }
    solver->setTimeout(0);
  }
  ObjectState *wos = state.addressSpace.getWriteable(mo, os);
  wos->write(offsetExpr, value);
  return true;
}

ObjectState *LocalExecutor::makeSymbolic(ExecutionState &state,
                                         const MemoryObject *mo,
                                         const ObjectState *os) {
  
  const ObjectState *clone = nullptr;
  
  if (os == nullptr) {
    os = state.addressSpace.findObject(mo);
  }
  if (os != nullptr) {
    if (state.isSymbolic(mo)) {
      return state.addressSpace.getWriteable(mo, os);
    }
    clone = new ObjectState(*os);
  }
  
  // Create a new object state for the memory object (instead of a copy).
  // Find a unique name for this array.  First try the original name,
  // or if that fails try adding a unique identifier.
  unsigned id = 0;
  std::string uniqueName = mo->name;
  while (!state.arrayNames.insert(uniqueName).second) {
    uniqueName = mo->name + "_" + llvm::utostr(++id);
  }
  const Array *array = arrayCache.CreateArray(uniqueName, mo->size);
  
  ObjectState *wos = bindObjectInState(state, mo, array);
  state.addSymbolic(mo, array);
  if (clone != nullptr) {
    wos->cloneWritten(clone);
    delete clone;
  }
  return wos;
}

MemoryObject *LocalExecutor::allocMemory(ExecutionState &state,
                                         size_t size,
                                         const llvm::Value *allocSite,
                                         MemKind kind,
                                         std::string name,
                                         size_t align) {

  MemoryObject *mo = memory->allocate(size, kind, allocSite, align);
  if (mo == nullptr) {
    klee_error("Could not allocate memory for symbolic allocation");
  }
  else {
    mo->name = name;
  }
  return mo;
}

MemoryObject *LocalExecutor::allocMemory(ExecutionState &state,
                                         llvm::Type *type,
                                         const llvm::Value *allocSite,
                                         MemKind kind,
                                         std::string name,
                                         size_t align,
                                         unsigned count) {

  if (align == 0) {
    align = kmodule->targetData->getPrefTypeAlignment(type);
  }
  uint64_t size = kmodule->targetData->getTypeStoreSize(type) * count;
  return allocMemory(state, size, allocSite, kind, name, align);
}

bool LocalExecutor::allocSymbolic(ExecutionState &state,
                                  size_t size,
                                  const llvm::Value *allocSite,
                                  MemKind kind,
                                  std::string name,
                                  WObjectPair &wop,
                                  size_t align) {

  MemoryObject *mo = allocMemory(state, size, allocSite, kind, name, align);
  if (mo != nullptr) {
    ObjectState *os = makeSymbolic(state, mo);
    wop.first = mo;
    wop.second = os;
    return true;
  }
  return false;
}

bool LocalExecutor::allocSymbolic(ExecutionState &state,
                                  Type *type,
                                  const llvm::Value *allocSite,
                                  MemKind kind,
                                  std::string name,
                                  WObjectPair &wop,
                                  size_t align,
                                  unsigned count) {

  MemoryObject *mo = allocMemory(state, type, allocSite, kind, name, align, count);
  if (mo != nullptr) {
    ObjectState *os = makeSymbolic(state, mo);
    wop.first = mo;
    wop.second = os;
    return true;
  }
  return false;
}

bool LocalExecutor::isLocallyAllocated(const ExecutionState &state, const MemoryObject *mo) const {

  const auto &allocas = state.stack.back().allocas;
  return allocas.find(mo) != allocas.end();
}


const Module *LocalExecutor::setModule(llvm::Module *module,
                                       const ModuleOptions &opts) {
  const Module *result = Executor::setModule(module, opts);

  for (std::vector<KFunction*>::iterator it = kmodule->functions.begin(),
           ie = kmodule->functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    for (unsigned i=0; i<kf->numInstructions; ++i)
      bindInstructionConstants(kf->instructions[i]);
  }
  return result;
}

void LocalExecutor::bindModuleConstants() {
  kmodule->constantTable = new Cell[kmodule->constants.size()];
  for (unsigned i=0; i<kmodule->constants.size(); ++i) {
    Cell &c = kmodule->constantTable[i];
    c.value = evalConstant(kmodule->constants[i]);
  }
}

void LocalExecutor::runFunctionUnconstrained(Function *f) {

  KFunction *kf = kmodule->functionMap[f];
  if (kf == nullptr) {
    // not in this compilation unit
    return;
  }
  
  std::string name = f->getName();
  outs() << "locally executing " << name << " ... ";
  ExecutionState *state = new ExecutionState(kf, name);
  
  if (pathWriter)
    state->pathOS = pathWriter->open();
  if (symPathWriter)
    state->symPathOS = symPathWriter->open();
  
  if (statsTracker)
    statsTracker->framePushed(*state, 0);
  
  initializeGlobals(*state);

  // create parameter values
  unsigned index = 0;
  for (Function::const_arg_iterator ai = f->arg_begin(), ae = f->arg_end(); ai != ae; ++ai, ++index) {
    
    const Argument &arg = *ai;
    std::string argName = arg.getName();
    Type *argType = arg.getType();
    size_t argAlign = arg.getParamAlignment();

    // RLR TODO: affirm that this is a fundamental type?
    WObjectPair wop;
    if (!allocSymbolic(*state, argType, &arg, MemKind::param, argName, wop, argAlign)) {
      klee_error("failed to allocate function parameter");
    }

    Expr::Width width = (unsigned) kmodule->targetData->getTypeAllocSizeInBits(argType);
    ref<Expr> e = wop.second->read(0, width);
    bindArgument(kf, index, *state, e);
  }
  
  processTree = new PTree(state);
  state->ptreeNode = processTree->root;
  run(*state);
  delete processTree;
  processTree = nullptr;

  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(NULL);

  // clean up global objects
  // RLR TODO: no real need to destroy the globals
  // and set them up again on next function. just need to
  // re-initialize
  legalFunctions.clear();
  globalObjects.clear();
  globalAddresses.clear();
  
  if (statsTracker)
    statsTracker->done();
  
  outs() << "done\n";
  outs().flush();
}
  
void LocalExecutor::runFunctionAsMain(Function *f,
                                      int argc,
                                      char **argv,
                                      char **envp) {
  
  std::vector<ref<Expr> > arguments;
  
  // force deterministic initialization of memory objects
//  srand(1);
//  srandom(1);
  
  MemoryObject *argvMO = nullptr;
  KFunction *kf = kmodule->functionMap[f];
  assert(kf && "main not found in this compilation unit");

  std::string name = f->getName();
  outs() << "locally executing " << name << " ... ";

  // In order to make uclibc happy and be closer to what the system is
  // doing we lay out the environments at the end of the argv array
  // (both are terminated by a null). There is also a final terminating
  // null that uclibc seems to expect, possibly the ELF header?
  
  int envc;
  for (envc=0; envp[envc]; ++envc) ;
  
  unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
  Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
  if (ai!=ae) {
    arguments.push_back(ConstantExpr::alloc(argc, Expr::Int32));
    if (++ai!=ae) {
      Instruction *first = static_cast<Instruction *>(f->begin()->begin());
      argvMO =
      memory->allocate((argc + 1 + envc + 1 + 1) * NumPtrBytes,
                       MemKind::param, first, 8);
      
      if (!argvMO)
        klee_error("Could not allocate memory for function arguments");
      
      arguments.push_back(argvMO->getBaseExpr());
      
      if (++ai!=ae) {
        uint64_t envp_start = argvMO->address + (argc+1)*NumPtrBytes;
        arguments.push_back(Expr::createPointer(envp_start));
        
        if (++ai!=ae)
          klee_error("invalid main function (expect 0-3 arguments)");
      }
    }
  }
  
  ExecutionState *state = new ExecutionState(kf, name);
  
  if (pathWriter)
    state->pathOS = pathWriter->open();
  if (symPathWriter)
    state->symPathOS = symPathWriter->open();

  if (statsTracker)
    statsTracker->framePushed(*state, 0);
  
  assert(arguments.size() == f->arg_size() && "wrong number of arguments");
  for (unsigned i = 0, e = f->arg_size(); i != e; ++i)
    bindArgument(kf, i, *state, arguments[i]);
  
  if (argvMO) {
    ObjectState *argvOS = bindObjectInState(*state, argvMO);
    
    for (int i=0; i<argc+1+envc+1+1; i++) {
      if (i==argc || i>=argc+1+envc) {
        // Write NULL pointer
        argvOS->write(i * NumPtrBytes, Expr::createPointer(0));
      } else {
        char *s = i<argc ? argv[i] : envp[i-(argc+1)];
        int j, len = strlen(s);
        
        MemoryObject *arg =
        memory->allocate(len + 1, MemKind::param, state->pc->inst, 8);
        if (!arg)
          klee_error("Could not allocate memory for function arguments");
        ObjectState *os = bindObjectInState(*state, arg);
        for (j=0; j<len+1; j++)
          os->write8(j, s[j]);
        
        // Write pointer to newly allocated and initialised argv/envp c-string
        argvOS->write(i * NumPtrBytes, arg->getBaseExpr());
      }
    }
  }
  
  initializeGlobals(*state);
  
  processTree = new PTree(state);
  state->ptreeNode = processTree->root;
  run(*state);
  delete processTree;
  processTree = 0;
  
  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(NULL);

  // clean up global objects
  // RLR TODO: no real need to destroy the globals
  // and set them up again on next function. just need to
  // re-initialize
  legalFunctions.clear();
  globalObjects.clear();
  globalAddresses.clear();
  
  if (statsTracker)
    statsTracker->done();

  outs() << "done\n";
  outs().flush();
}
  
void LocalExecutor::run(ExecutionState &initialState) {

  bindModuleConstants();

  // Delay init till now so that ticks don't accrue during
  // optimization and such.
  initTimers();
  
  states.insert(&initialState);
  
  searcher = constructUserSearcher(*this);
  
  std::vector<ExecutionState *> newStates(states.begin(), states.end());
  searcher->update(0, newStates, std::vector<ExecutionState *>());
  
  while (!states.empty() && !haltExecution) {
    ExecutionState &state = searcher->selectState();
    KInstruction *ki = state.pc;
    stepInstruction(state);

    executeInstruction(state, ki);

    processTimers(&state, 0);
    checkMemoryUsage();
    updateStates(&state);
  }
  
  delete searcher;
  searcher = 0;
  
  doDumpStates();
}

void LocalExecutor::executeInstruction(ExecutionState &state, KInstruction *ki) {
  Instruction *i = ki->inst;
  switch (i->getOpcode()) {
      // Control flow

    case Instruction::Br: {
      auto &branches = state.branches;
      if (branches.find(ki) == branches.end()) {

        // not a back-edge
        branches.insert(ki);
        Executor::executeInstruction(state, ki);
      } else {
        // this state has been here before. just terminate early.
        terminateStateOnExit(state);
      }
      break;
    }
      
    case Instruction::Invoke:
    case Instruction::Call: {
      const CallInst *ci = cast<CallInst>(i);
      Function *f = ci->getCalledFunction();

      // if this is not a function in this module, let
      // the standard executor handle it.
      std::string fnName = f->getName();

      if (fnInModule.find(fnName) == fnInModule.end()) {

        // if this is a call to mark(), then log the marker to state
        if ((f->getName().upper() == "MARK") &&
            (f->arg_size() == 2) &&
            (f->getReturnType()->isVoidTy())) {

          const Constant *arg0 = dyn_cast<Constant>(ci->getArgOperand(0));
          const Constant *arg1 = dyn_cast<Constant>(ci->getArgOperand(1));
          if ((arg0 != nullptr) && (arg1 != nullptr)) {
            unsigned fnID = (unsigned) arg0->getUniqueInteger().getZExtValue();
            unsigned bbID = (unsigned) arg1->getUniqueInteger().getZExtValue();
            state.addMarker(fnID, bbID);
          }
        } else if (fnName == "abort" || fnName == "exit") {
          terminateStateOnExit(state);
        } else {
          Executor::executeInstruction(state, ki);
        }
        return;
      }

      // hence, this is a function in this module
      Type *ty = f->getReturnType();
      std::string name = f->getName();
      unsigned counter = state.callTargetCounter[name]++;
      if (!ty->isVoidTy()) {

        WObjectPair wop;
        if (ty->isPointerTy()) {

          Type *subtype = ty->getPointerElementType();
          allocSymbolic(state, subtype, i, MemKind::output, fullName(name, counter, "return"), wop, 0, lazyAllocationCount);
          bindLocal(ki, state, wop.first->getBaseExpr());
        } else {

          // RLR TODO: must this then be a fundamental type?
          if (!allocSymbolic(state, ty, i, MemKind::output, fullName(name, counter, "return"), wop)) {
            klee_error("failed to allocate called function parameter");
          }
          Expr::Width width = (unsigned) kmodule->targetData->getTypeAllocSizeInBits(ty);
          ref<Expr> e = wop.second->read(0, width);
          bindLocal(ki, state, e);
        }
      }
      
      // now for the arguments
      unsigned index = 1;
      for (auto itr = f->arg_begin(), end=f->arg_end(); itr != end; ++itr, ++index) {
        const Argument &arg = *itr;
        Type *type = arg.getType();

        // check the level of ptr indirection (if any)
        const unsigned count = countLoadIndirection(type);

        if (count > 0) {

          // RLR TODO: check for const (not available to LLVM IR)
          ref<Expr> address = eval(ki, index, state).value;
          Expr::Width width = address.get()->getWidth();
          assert(width == Context::get().getPointerWidth());

          ObjectPair op;
          if (resolveMO(state, address, op)) {
            const MemoryObject *orgMO = op.first;
            const ObjectState *orgOS = op.second;
            unsigned size = orgMO->size;
            ObjectState *wos = state.addressSpace.getWriteable(orgMO, orgOS);

            WObjectPair wop;
            if (!allocSymbolic(state, size, &arg, MemKind::output, fullName(name, counter, arg.getName()), wop, orgMO->align)) {
              klee_error("failed to allocate ptr argument");
            }
            ObjectState *newOS = wop.second;
            for (unsigned offset = 0; offset < size; ++offset) {
              wos->write(offset, newOS->read8(offset));
            }
          }
        }
      }
      break;
    }

      // Memory instructions...
      
    case Instruction::Alloca: {
      AllocaInst *ai = cast<AllocaInst>(i);
      unsigned elementSize = (unsigned)
      kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
      ref<Expr> size = Expr::createPointer(elementSize);
      if (ai->isArrayAllocation()) {
        ref<Expr> count = eval(ki, 0, state).value;
        count = Expr::createZExtToPointerWidth(count);
        size = MulExpr::create(size, count);
      }
      executeAlloc(state, size, MemKind::alloca, ki);
      break;
    }

    case Instruction::GetElementPtr: {
      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
      ref<Expr> base = eval(ki, 0, state).value;

      ObjectPair op;
      if (resolveMO(state, base, op)) {
        const MemoryObject *mo = op.first;

        assert(i->getType()->isPtrOrPtrVectorTy());
        Expr::Width width = getWidthForLLVMType(i->getType()->getPointerElementType());
        unsigned bytes = Expr::getMinBytesForWidth(width);

        for (std::vector<std::pair<unsigned, uint64_t> >::iterator
                 it = kgepi->indices.begin(), ie = kgepi->indices.end();
             it != ie; ++it) {
          uint64_t elementSize = it->second;
          ref<Expr> index = eval(ki, it->first, state).value;

          base = AddExpr::create(base,
                                 MulExpr::create(Expr::createSExtToPointerWidth(index),
                                                 Expr::createPointer(elementSize)));
        }
        if (kgepi->offset)
          base = AddExpr::create(base,
                                 Expr::createPointer(kgepi->offset));

        solver->setTimeout(coreSolverTimeout);
        ref<Expr> mc = mo->getBoundsCheckPointer(base, bytes);

        if (AssumeInboundPointers) {
          bool inBounds;
          if (!solver->mayBeTrue(state, mc, inBounds) || !inBounds) {
            solver->setTimeout(0);
            state.pc = state.prevPC;
            terminateStateEarly(state, "gep optimistic offset failure.");
          }
          addConstraint(state, mc);
        } else {
          klee_error("non-optimistic not supported at this time");
        }
        solver->setTimeout(0);
      }
      bindLocal(ki, state, base);
      break;
    }

    case Instruction::Load: {
      LoadInst *li = cast<LoadInst>(i);
      const Value *v = li->getPointerOperand();
      Type *type = v->getType();
      ref<Expr> base = eval(ki, 0, state).value;

      executeReadMemoryOperation(state, base, type, ki);
      break;
    }
      
    case Instruction::Store: {
      StoreInst *si = cast<StoreInst>(i);
      const Value *v = si->getValueOperand();
      std::string name;
      if (v->hasName()) {
        name = v->getName();
      }
      
      ref<Expr> base = eval(ki, 1, state).value;
      ref<Expr> value = eval(ki, 0, state).value;
      executeWriteMemoryOperation(state, base, value, name);
      break;
    }
      
    default:
      Executor::executeInstruction(state, ki);
      break;
    }
  }
  
unsigned LocalExecutor::countLoadIndirection(const llvm::Type* type) const {
  
  unsigned counter = 0;

  while (type->isPointerTy()) {
    counter++;
    type = type->getPointerElementType();
  }
  return counter;
}
  
Interpreter *Interpreter::createLocal(LLVMContext &ctx,
                                      const InterpreterOptions &opts,
                                      InterpreterHandler *ih,
                                      const std::set<std::string> &fnInModule) {
  return new LocalExecutor(ctx, opts, ih, fnInModule);
}
  
  
  
}

///

