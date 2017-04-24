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
#include "Memory.h"
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
  
  
// static utility functions
  
static std::string getFQFnName(const Function *f) {

  std::string result = f->getParent()->getModuleIdentifier() + "::" + f->getName().str();
  return result;
}
  
LocalExecutor::LocalExecutor(LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih,
                             const std::set<Function *> &fns) :
Executor(ctx, opts, ih),
lazyAllocationCount(8),
iterationBound(1),
fnInModule(fns)
{
    
}

LocalExecutor::~LocalExecutor() {
    
    
}

bool LocalExecutor::resolveMO(ExecutionState &state, ref<Expr> address, ObjectPair &op) {

  bool result = false;

  address = state.constraints.simplifyExpr(address);
  assert(address.get()->getWidth() == Context::get().getPointerWidth());

  if (isa<ConstantExpr>(address)) {
    ref<ConstantExpr> caddress = cast<ConstantExpr>(address);

    // fast path: single in-bounds resolution
    result = state.addressSpace.resolveOne(caddress, op);
  }
  if (!result) {

    // not a const address, so we have to ask the solver
    solver->setTimeout(coreSolverTimeout);
    if (!state.addressSpace.resolveOne(state, solver, address, op, result)) {
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

  ref<Expr> offsetExpr = state.constraints.simplifyExpr(mo->getOffsetExpr(address));
  if (isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> coffsetExpr = cast<ConstantExpr>(offsetExpr);
    const unsigned offset = (unsigned) coffsetExpr->getZExtValue();
    if (offset + bytes > mo->size) {
      terminateStateOnError(state, "memory error: out of bound pointer", Ptr,
                            NULL, getAddressInfo(state, address));
      return false;
    }
  } else {

    bool inBounds;
    bool success;
    solver->setTimeout(coreSolverTimeout);

    ref<Expr> mc = mo->getBoundsCheckOffset(offsetExpr, bytes);
    success = solver->mustBeTrue(state, mc, inBounds);

    if (success && !inBounds && AssumeInboundPointers) {

      // not in bounds, so add constraint and try, try, again
      klee_warning("cannot prove pointer inbounds, adding constraint");
      addConstraint(state, mc);
      success = solver->mustBeTrue(state, mc, inBounds);
    }

    solver->setTimeout(0);
    if (!success || !inBounds) {
      state.pc = state.prevPC;
      terminateStateEarly(state, "Failed to resolve read memory offset.");
      return false;
    }
  }

  if (!state.isSymbolic(mo) && !state.isLocallyAllocated(mo)) {
    os = makeSymbolic(state, mo, os);
  }
  
  ref<Expr> e = os->read(offsetExpr, width);
  bindLocal(target, state, e);
  
  if ((countLoadIndirection(type) > 1) &&
      (isUnconstrainedPtr(state, e))) {
    // this is an unconstrained ptr-ptr. allocate something behind the pointer

    Type *subtype = type->getPointerElementType()->getPointerElementType();
    MemoryObject *newMO = allocMemory(state, lazyAllocationCount, subtype, 0,
                                      target->inst, mo->isGlobal, '*' + mo->name);
//    newOS->pointsTo = newMO;
    bindObjectInState(state, newMO, mo->isLocal);
    
    // and constrain this pointer to point at it.
    ref<ConstantExpr> ptr = newMO->getBaseExpr();
    ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(e, ptr));
    state.addConstraint(eq);
  }
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
  if ((mo->name == MemoryObject::unnamed) && (!name.empty())) {
    mo->name = name;
  }

  ref<Expr> offsetExpr = state.constraints.simplifyExpr(mo->getOffsetExpr(address));
  if (isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> coffsetExpr = cast<ConstantExpr>(offsetExpr);
    const unsigned offset = (unsigned) coffsetExpr->getZExtValue();
    if (offset + bytes > mo->size) {

      terminateStateOnError(state, "memory error: out of bound pointer", Ptr,
                            NULL, getAddressInfo(state, address));
      return false;
    }
  } else {
    bool inBounds;
    bool success;
    solver->setTimeout(coreSolverTimeout);

    ref<Expr> mc = mo->getBoundsCheckOffset(offsetExpr, bytes);
    success = solver->mustBeTrue(state, mc, inBounds);

    if (success && !inBounds && AssumeInboundPointers) {

      // not in bounds, so add constraint and try, try, again
      klee_warning("cannot prove pointer inbounds, adding constraint");
      addConstraint(state, mc);
      success = solver->mustBeTrue(state, mc, inBounds);
    }

    solver->setTimeout(0);
    if (!success || !inBounds) {
      state.pc = state.prevPC;
      terminateStateEarly(state, "Failed to resolve write memory offset.");
      return false;
    }
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
  
  ObjectState *wos = bindObjectInState(state, mo, mo->isLocal, array);
  state.addSymbolic(mo, array);
  if (clone != nullptr) {
    wos->cloneWritten(clone);
    delete clone;
  }
  return wos;
}

MemoryObject *LocalExecutor::allocMemory(ExecutionState &state,
                                         unsigned count,
                                         llvm::Type *type,
                                         size_t align,
                                         const llvm::Value *allocSite,
                                         bool isGlobal,
                                         std::string name) {

  if (align == 0) {
    align = kmodule->targetData->getPrefTypeAlignment(type);
  }
  uint64_t size = kmodule->targetData->getTypeStoreSize(type);
  size *= count;
  return allocMemory(state, size, align, allocSite, isGlobal, name);
}

MemoryObject *LocalExecutor::allocMemory(ExecutionState &state,
                                         size_t size,
                                         size_t align,
                                         const llvm::Value *allocSite,
                                         bool isGlobal,
                                         std::string name) {

  MemoryObject *mo = memory->allocate(size, !isGlobal, isGlobal, allocSite, align);
  if (mo == nullptr) {
    klee_error("Could not allocate memory for symbolic allocation");
  }
  else {
    mo->setName(name);
  }
  return mo;
}

ref<Expr> LocalExecutor::allocSymbolic(ExecutionState &state,
                                       unsigned count,
                                       Type *type,
                                       size_t align,
                                       const llvm::Value *allocSite,
                                       bool isGlobal,
                                       std::string name ) {

  MemoryObject *mo = allocMemory(state, count, type, align, allocSite, isGlobal, name);
  if (mo != nullptr) {
    ObjectState *os = makeSymbolic(state, mo);
    Expr::Width width = getWidthForLLVMType(type);
    return os->read(0, width);
  }
  return Expr::createPointer(0);
}


ref<Expr> LocalExecutor::allocSymbolic(ExecutionState &state,
                                       size_t size,
                                       size_t align,
                                       const llvm::Value *allocSite,
                                       bool isGlobal,
                                       std::string name,
                                       ObjectPair &op) {

  op.first = nullptr;
  op.second = nullptr;
  MemoryObject *mo = allocMemory(state, size, align, allocSite, isGlobal, name);
  if (mo != nullptr) {
    ObjectState *os = makeSymbolic(state, mo);
    op.first = mo;
    op.second = os;
    return Expr::createPointer(mo->address);
  }
  return Expr::createPointer(0);
}

void LocalExecutor::runFunctionUnconstrained(Function *f) {

  assert((fnInModule.find(f) != fnInModule.end()) && "unconstrained function not in module");

  KFunction *kf = kmodule->functionMap[f];
  if (kf == nullptr) {
    // not in this compilation unit
    return;
  }
  
  std::string name = getFQFnName(f);
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
  for (Function::const_arg_iterator ai = f->arg_begin(), ae = f->arg_end(); ai != ae; ++ai) {
    
    const Argument &arg = *ai;
    std::string argName = arg.getName();
    Type *argType = arg.getType();
    size_t argAlign = arg.getParamAlignment();

    ref<Expr> e = allocSymbolic(*state, 1, argType, argAlign, &arg, false, argName);
    bindArgument(kf, index, *state, e);
    index++;
  }
  
  processTree = new PTree(state);
  state->ptreeNode = processTree->root;
  run(*state);
  delete processTree;
  processTree = nullptr;
  
  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(NULL);
  
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

  std::string name = getFQFnName(f);
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
                       /*isLocal=*/false, /*isGlobal=*/true,
                       /*allocSite=*/first, /*alignment=*/8);
      
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
    ObjectState *argvOS = bindObjectInState(*state, argvMO, false);
    
    for (int i=0; i<argc+1+envc+1+1; i++) {
      if (i==argc || i>=argc+1+envc) {
        // Write NULL pointer
        argvOS->write(i * NumPtrBytes, Expr::createPointer(0));
      } else {
        char *s = i<argc ? argv[i] : envp[i-(argc+1)];
        int j, len = strlen(s);
        
        MemoryObject *arg =
        memory->allocate(len + 1, /*isLocal=*/false, /*isGlobal=*/true,
                         /*allocSite=*/state->pc->inst, /*alignment=*/8);
        if (!arg)
          klee_error("Could not allocate memory for function arguments");
        ObjectState *os = bindObjectInState(*state, arg, false);
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
      unsigned counterValue = state.iterationCounter[ki];
      if (counterValue > iterationBound) {
        // kill state
        terminateState(state);
        return;
      }
      state.iterationCounter[ki] = counterValue + 1;
      Executor::executeInstruction(state, ki);
      break;
    }
      
    case Instruction::Invoke:
    case Instruction::Call: {
      const CallInst *ci = cast<CallInst>(i);
      Function *f = ci->getCalledFunction();

      // if this is not a function in module, let
      // the standard executor handle it.
      if (fnInModule.find(f) == fnInModule.end()) {
        return Executor::executeInstruction(state, ki);
      }

      // hence, this is a function in this module
      Type *ty = f->getReturnType();
      std::string name = getFQFnName(f);
      unsigned counter = state.callTargetCounter[name]++;
      if (!ty->isVoidTy()) {

        if (ty->isPointerTy()) {
          // RLR TODO: handle pointer return types
          klee_error("what to do with pointer types");
        } else {
          ref<Expr> e = allocSymbolic(state, 1, ty, 0, i, false, fullName(name, counter, "return"));
          bindLocal(ki, state, e);
        }
      }
      
      // now for the arguments
      unsigned index = 1;
      for (auto itr = f->arg_begin(), end=f->arg_end(); itr != end; ++itr, ++index) {
        const Argument &arg = *itr;
        Type *type = arg.getType();
        const unsigned align = arg.getParamAlignment();

        // check the level of ptr indirection (if any)
        const unsigned count = countLoadIndirection(type);

        if (count > 0) {

          // RLR TODO: check for const (not available to LLVM IR)
          ref<Expr> address = eval(ki, index, state).value;
          unsigned width = address.get()->getWidth();
          assert(width == Context::get().getPointerWidth());

          if (count == 1) {
            ObjectPair op;
            if (resolveMO(state, address, op)) {
              const MemoryObject *orgMO = op.first;
              const ObjectState *orgOS = op.second;
              unsigned size = orgMO->size;
              allocSymbolic(state, size, orgMO->align, &arg, false, fullName(name, counter, arg.getName()), op);
              const MemoryObject *newMO = op.first;
              const ObjectState *newOS = op.second;

              ObjectState *wos = state.addressSpace.getWriteable(newMO, newOS);
              for (unsigned offset = 0; offset < size; ++offset) {
                wos->write(offset, orgOS->read8(offset));
              }
            }

          } else {
            // target is a ptr-...-ptr. just mark it as unconstrained
            // and let lazy init take care of the rest
            ref<Expr> value = allocSymbolic(state, 1, type, align, &arg, false, fullName(name, counter, arg.getName()));
            executeWriteMemoryOperation(state, address, value, "");
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
      executeAlloc(state, size, true, ki);
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
                                      const std::set<Function *> &fnInModule) {
  return new LocalExecutor(ctx, opts, ih, fnInModule);
}
  
  
  
}

///

