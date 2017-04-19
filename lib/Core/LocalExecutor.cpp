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
//#include "Callsite.h"

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
                             InterpreterHandler *ih) :
Executor(ctx, opts, ih),
lazyAllocationCount(8) {
    
}

LocalExecutor::~LocalExecutor() {
    
    
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
  
bool LocalExecutor::executeFastReadMemoryOperation(ExecutionState &state,
                                                  ref<Expr> address,
                                                  const Type *type,
                                                  KInstruction *target) {
    
  // fast read requires address to be a const expression
  if (!isa<ConstantExpr>(address)) return false;
  ref<ConstantExpr> caddress = cast<ConstantExpr>(address);
  
  Expr::Width width = getWidthForLLVMType(target->inst->getType());
  unsigned bytes = Expr::getMinBytesForWidth(width);
    
  // fast path: single in-bounds resolution
  ObjectPair op;
  if (!state.addressSpace.resolveOne(caddress, op)) return false;

  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  ref<Expr> offsetExpr = state.constraints.simplifyExpr(mo->getOffsetExpr(caddress));
  if (!isa<ConstantExpr>(offsetExpr)) return false;
  const unsigned offset = cast<ConstantExpr>(offsetExpr)->getZExtValue();
  if (offset + bytes > mo->size) {
      
    terminateStateOnError(state, "memory error: out of bound pointer", Ptr,
                          NULL, getAddressInfo(state, address));
    return true;
  }

  if (!state.isSymbolic(mo)) {
    os = makeSymbolic(state, mo, os);
  }
  
  ref<Expr> result = os->read(offset, width);
  bindLocal(target, state, result);
  
  if ((countLoadIndirection(type) > 1) &&
      (isUnconstrainedPtr(state, result))) {
    // this is an unconstrained ptr-ptr. allocate something behind the pointer
    
    Type *subtype = type->getPointerElementType()->getPointerElementType();
    uint64_t size = kmodule->targetData->getTypeStoreSize(subtype);
    size *= lazyAllocationCount;
    
    size_t align = kmodule->targetData->getPrefTypeAlignment(subtype);
    MemoryObject *newMO = memory->allocate(size,
                                           mo->isLocal,
                                           mo->isGlobal,
                                           target->inst,
                                           align);
    newMO->setName(mo->name + "*");
//    newOS->pointsTo = newMO;
    bindObjectInState(state, newMO, mo->isLocal);
    
    // and constrain this pointer to point at it.
    ref<ConstantExpr> ptr = newMO->getBaseExpr();
    ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(result, ptr));
    state.addConstraint(eq);
  }
  
  return true;
}
  
bool LocalExecutor::executeFastWriteMemoryOperation(ExecutionState &state,
                                                 ref<Expr> address,
                                                 ref<Expr> value,
                                                 const std::string name) {
    
  // fast write requires address to be a const expression
  if (!isa<ConstantExpr>(address)) return false;
  ref<ConstantExpr> caddress = cast<ConstantExpr>(address);
    
  Expr::Width width = value->getWidth();
  unsigned bytes = Expr::getMinBytesForWidth(width);
    
  // fast path: single in-bounds resolution
  ObjectPair op;
  if (!state.addressSpace.resolveOne(caddress, op)) return false;
    
  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;
  
  // override address name, if unset
  if ((mo->name == MemoryObject::unnamed) &&
      (!name.empty())) {
    mo->name = name;
  }
  
  ref<Expr> offsetExpr = state.constraints.simplifyExpr(mo->getOffsetExpr(caddress));
  if (!isa<ConstantExpr>(offsetExpr)) return false;
  const unsigned offset = cast<ConstantExpr>(offsetExpr)->getZExtValue();
  if (offset + bytes > mo->size) {
      
    terminateStateOnError(state, "memory error: out of bound pointer", Ptr,
                          NULL, getAddressInfo(state, address));
    return true;
  }
  if (os->readOnly) {
    terminateStateOnError(state, "memory error: object read only",
                          ReadOnly);
  } else {
    ObjectState *wos = state.addressSpace.getWriteable(mo, os);
    wos->write(offset, value);
  }
  return true;
}

void LocalExecutor::executeReadMemoryOperation(ExecutionState &state,
                                               ref<Expr> address,
                                               const llvm::Type *type,
                                               KInstruction *target) {
  
  Expr::Width width =  getWidthForLLVMType(target->inst->getType());
  unsigned bytes = Expr::getMinBytesForWidth(width);
  address = state.constraints.simplifyExpr(address);
  
  // fast path: single in-bounds resolution
  ObjectPair op;
  bool success;
  solver->setTimeout(coreSolverTimeout);
  if (!state.addressSpace.resolveOne(state, solver, address, op, success)) {
    address = toConstant(state, address, "resolveOne failure");
    success = state.addressSpace.resolveOne(cast<ConstantExpr>(address), op);
  }
  solver->setTimeout(0);
  
  if (success) {
    const MemoryObject *mo = op.first;
    ref<Expr> offset = mo->getOffsetExpr(address);
    
    bool inBounds;
    solver->setTimeout(coreSolverTimeout);
    
    // RLR: probably not the best way to do this
    // RLR TODO: why always do this. most of the time offset should be a const expression of 0.
    ref<Expr> mc = mo->getBoundsCheckOffset(offset, bytes);
    bool success = solver->mustBeTrue(state, mc, inBounds);
    
    if (AssumeInboundPointers && success && !inBounds) {
      
      // not in bounds, so add constraint and try, try, again
      klee_warning("cannot prove pointer inbounds, adding constraint");
      ExprPPrinter::printOne(llvm::errs(), "Expr", mc);
      addConstraint(state, mc);
      success = solver->mustBeTrue(state, mc, inBounds);
    }
    
    solver->setTimeout(0);
    if (!success) {
      state.pc = state.prevPC;
      terminateStateEarly(state, "Query timed out (bounds check).");
      return;
    }
    
    if (inBounds) {
      
      const ObjectState *os = op.second;
      if (!state.isSymbolic(mo)) {
        os = makeSymbolic(state, mo, os);
      }
      
      ref<Expr> result = os->read(offset, width);
      bindLocal(target, state, result);
      
      if ((countLoadIndirection(type) > 1) &&
          (isUnconstrainedPtr(state, result))) {
        // this is an unconstrained ptr-ptr. allocate something behind the pointer
        
        Type *subtype = type->getPointerElementType()->getPointerElementType();
        uint64_t size = kmodule->targetData->getTypeStoreSize(subtype);
        size *= lazyAllocationCount;
        
        size_t align = kmodule->targetData->getPrefTypeAlignment(subtype);
        MemoryObject *newMO = memory->allocate(size,
                                               mo->isLocal,
                                               mo->isGlobal,
                                               target->inst,
                                               align);
        newMO->setName("*" + mo->name);
        //    newOS->pointsTo = newMO;
        bindObjectInState(state, newMO, mo->isLocal);
        
        // and constrain this pointer to point at it.
        ref<ConstantExpr> ptr = newMO->getBaseExpr();
        ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(result, ptr));
        state.addConstraint(eq);
      }
      
      return;
    }
  }
  
  // we are on an error path (no resolution, multiple resolution, one
  // resolution with out of bounds)
  state.pc = state.prevPC;
  terminateStateEarly(state, "Failed to resolve memory load.");
  return;
}
  
void LocalExecutor::executeWriteMemoryOperation(ExecutionState &state,
                                                ref<Expr> address,
                                                ref<Expr> value,
                                                const std::string name) {
  
  Expr::Width width = value->getWidth();
  unsigned bytes = Expr::getMinBytesForWidth(width);
  address = state.constraints.simplifyExpr(address);
  value = state.constraints.simplifyExpr(value);
  
  // fast path: single in-bounds resolution
  ObjectPair op;
  bool success;
  solver->setTimeout(coreSolverTimeout);
  if (!state.addressSpace.resolveOne(state, solver, address, op, success)) {
    address = toConstant(state, address, "resolveOne failure");
    success = state.addressSpace.resolveOne(cast<ConstantExpr>(address), op);
  }
  solver->setTimeout(0);
  
  if (success) {
    const MemoryObject *mo = op.first;
    
    ref<Expr> offset = mo->getOffsetExpr(address);
    
    bool inBounds;
    solver->setTimeout(coreSolverTimeout);
    
    // RLR: probably not the best way to do this
    // RLR TODO: why always do this. most of the time offset should be a const expression of 0.
    ref<Expr> mc = mo->getBoundsCheckOffset(offset, bytes);
    bool success = solver->mustBeTrue(state, mc, inBounds);
    
    if (AssumeInboundPointers && success && !inBounds) {
      
      // not in bounds, so add constraint and try, try, again
      klee_warning("cannot prove pointer inbounds, adding constraint");
      ExprPPrinter::printOne(llvm::errs(), "Expr", mc);
      addConstraint(state, mc);
      success = solver->mustBeTrue(state, mc, inBounds);
    }
    
    solver->setTimeout(0);
    if (!success) {
      state.pc = state.prevPC;
      terminateStateEarly(state, "Query timed out (bounds check).");
      return;
    }
    
    if (inBounds) {
      const ObjectState *os = op.second;
      if (os->readOnly) {
        terminateStateOnError(state, "memory error: object read only",
                              ReadOnly);
      } else {
        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
        wos->write(offset, value);
      }
      return;
    }
  }
  
  // we are on an error path (no resolution, multiple resolution, one
  // resolution with out of bounds)
  state.pc = state.prevPC;
  terminateStateEarly(state, "Failed to resolve memory store operation.");
  return;
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

void LocalExecutor::runFunctionUnconstrained(Function *f) {

  KFunction *kf = kmodule->functionMap[f];
  if (kf == nullptr) {
    // not in this compilation unit
    return;
  }
  
  std::string name = getFQFnName(f);
  ExecutionState *state = new ExecutionState(kf, &name);
  
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
    
    const Argument *arg = static_cast<const Argument *>(ai);
    std::string argName = arg->getName();
    Type *argType = arg->getType();
    uint64_t argSize = kmodule->targetData->getTypeStoreSize(argType);
    
    // get an alignment for this argument
    size_t argAlign = arg->getParamAlignment();
    if (argAlign == 0) {
      argAlign = kmodule->targetData->getPrefTypeAlignment(argType);
    }
    Expr::Width width = getWidthForLLVMType(argType);
    MemoryObject *mo = memory->allocate(argSize, false, true, arg, argAlign);
    mo->setName(argName);
    
    if (mo == nullptr) {
      klee_error("Could not allocate memory for function arguments");
    }
    
    ObjectState *os = makeSymbolic(*state, mo);
    ref<Expr> e = os->read(0, width);
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
}
  
void LocalExecutor::runFunctionAsMain(Function *f,
                                      int argc,
                                      char **argv,
                                      char **envp) {
  
#ifdef NEVER
  std::vector<ref<Expr> > arguments;
  
  // force deterministic initialization of memory objects
  srand(1);
  srandom(1);
  
  MemoryObject *argvMO = 0;
  
  // In order to make uclibc happy and be closer to what the system is
  // doing we lay out the environments at the end of the argv array
  // (both are terminated by a null). There is also a final terminating
  // null that uclibc seems to expect, possibly the ELF header?
  
  int envc;
  for (envc=0; envp[envc]; ++envc) ;
  
  unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
  KFunction *kf = kmodule->functionMap[f];
  assert(kf);
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
  
  ExecutionState *state = new ExecutionState(kmodule->functionMap[f]);
  
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
#endif
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

#ifdef NOTYET
    case Instruction::Ret: {
      ReturnInst *ri = cast<ReturnInst>(i);
      KInstIterator kcaller = state.stack.back().caller;
      Instruction *caller = kcaller ? kcaller->inst : 0;
      bool isVoidReturn = (ri->getNumOperands() == 0);
      ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);
      
      if (!isVoidReturn) {
        result = eval(ki, 0, state).value;
      }
      
      if (state.stack.size() <= 1) {
        assert(!caller && "caller set on initial stack frame");
        terminateStateOnExit(state);
      } else {
        state.popFrame();
        
        if (statsTracker)
          statsTracker->framePopped(state);
        
        if (InvokeInst *ii = dyn_cast<InvokeInst>(caller)) {
          transferToBasicBlock(ii->getNormalDest(), caller->getParent(), state);
        } else {
          state.pc = kcaller;
          ++state.pc;
        }
        
        if (!isVoidReturn) {
          LLVM_TYPE_Q Type *t = caller->getType();
          if (t != Type::getVoidTy(i->getContext())) {
            // may need to do coercion due to bitcasts
            Expr::Width from = result->getWidth();
            Expr::Width to = getWidthForLLVMType(t);
            
            if (from != to) {
              CallSite cs = (isa<InvokeInst>(caller) ? CallSite(cast<InvokeInst>(caller)) :
                             CallSite(cast<CallInst>(caller)));
              
              // XXX need to check other param attrs ?
              bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
              if (isSExt) {
                result = SExtExpr::create(result, to);
              } else {
                result = ZExtExpr::create(result, to);
              }
            }
            
            bindLocal(kcaller, state, result);
          }
        } else {
          // We check that the return value has no users instead of
          // checking the type, since C defaults to returning int for
          // undeclared functions.
          if (!caller->use_empty()) {
            terminateStateOnExecError(state, "return void when caller expected a result");
          }
        }
      }
      break;
    }
#endif
      
#ifdef NOTYET
    case Instruction::Br: {
      BranchInst *bi = cast<BranchInst>(i);
      if (bi->isUnconditional()) {
        transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), state);
      } else {
        // FIXME: Find a way that we don't have this hidden dependency.
        assert(bi->getCondition() == bi->getOperand(0) &&
               "Wrong operand index!");
        ref<Expr> cond = eval(ki, 0, state).value;
        Executor::StatePair branches = fork(state, cond, false);
        
        // NOTE: There is a hidden dependency here, markBranchVisited
        // requires that we still be in the context of the branch
        // instruction (it reuses its statistic id). Should be cleaned
        // up with convenient instruction specific data.
        if (statsTracker && state.stack.back().kf->trackCoverage)
          statsTracker->markBranchVisited(branches.first, branches.second);
        
        if (branches.first)
          transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), *branches.first);
        if (branches.second)
          transferToBasicBlock(bi->getSuccessor(1), bi->getParent(), *branches.second);
      }
      break;
    }
#endif
      
    case Instruction::Invoke:
    case Instruction::Call: {
      
      CallSite cs(i);
      
      // have to setup for a function call in case this is a call
      // to a klee internal handler
      unsigned numArgs = cs.arg_size();
      Value *fp = cs.getCalledValue();
      Function *f = getTargetFunction(fp, state);
      
      if (isa<InlineAsm>(fp)) {
        terminateStateOnExecError(state, "inline assembly is unsupported");
        break;
      }
      
      // evaluate arguments
      std::vector< ref<Expr> > arguments;
      arguments.reserve(numArgs);
      
      for (unsigned j=0; j<numArgs; ++j)
        arguments.push_back(eval(ki, j+1, state).value);
      
      if (f != nullptr) {
        const FunctionType *fType =
        dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
        const FunctionType *fpType =
        dyn_cast<FunctionType>(cast<PointerType>(fp->getType())->getElementType());
        
        // special case the call with a bitcast case
        if (fType != fpType) {
          assert(fType && fpType && "unable to get function type");
          
          // XXX check result coercion
          
          // XXX this really needs thought and validation
          unsigned i=0;
          for (std::vector< ref<Expr> >::iterator
               ai = arguments.begin(), ie = arguments.end();
               ai != ie; ++ai) {
            Expr::Width to, from = (*ai)->getWidth();
            
            if (i<fType->getNumParams()) {
              to = getWidthForLLVMType(fType->getParamType(i));
              
              if (from != to) {
                // XXX need to check other param attrs ?
                bool isSExt = cs.paramHasAttr(i+1, llvm::Attribute::SExt);
                if (isSExt) {
                  arguments[i] = SExtExpr::create(arguments[i], to);
                } else {
                  arguments[i] = ZExtExpr::create(arguments[i], to);
                }
              }
            }
            
            i++;
          }
        }
        if (f->isDeclaration() && (f->getIntrinsicID() == Intrinsic::not_intrinsic)) {
          if (specialFunctionHandler->handle(state, f, ki, arguments)) {
            
            // this was an handled by the specialFunctionHandler, so we can return
            return;
          }
        }
      }
      
      Type *ty = f->getReturnType();
      if (!ty->isVoidTy()) {
        
        uint64_t size = kmodule->targetData->getTypeStoreSize(ty);
        Expr::Width width = getWidthForLLVMType(ty);
        
        // get an alignment for this value
        size_t align = 8;
        if (ty->isSized()) {
          align = kmodule->targetData->getPrefTypeAlignment(ty);
        }
        
        std::string name = getFQFnName(f);
        unsigned counter = state.callTargetCounter[name]++;
        MemoryObject *mo = memory->allocate(size, false, true, i, align);
        mo->setName(name + "::" + std::to_string(counter) + "::return");
        
        if (mo == nullptr) {
          klee_error("Could not allocate memory for function arguments");
        }
        
        ObjectState *os = makeSymbolic(state, mo);
        ref<Expr> e = os->read(0, width);
        bindLocal(ki, state, e);
        
      }
      break;
    }

    case Instruction::PHI: {
      ref<Expr> result = eval(ki, state.incomingBBIndex, state).value;
      bindLocal(ki, state, result);
      break;
    }
      
      // Memory instructions...
      
    case Instruction::Alloca: {
      AllocaInst *ai = cast<AllocaInst>(i);
      unsigned elementSize =
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

      
#ifdef NOTYET
      
    case Instruction::GetElementPtr: {
      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
      ref<Expr> base = eval(ki, 0, state).value;
      
      for (std::vector< std::pair<unsigned, uint64_t> >::iterator
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
      bindLocal(ki, state, base);
      break;
    }
      
#endif
      
    case Instruction::Load: {
      LoadInst *li = cast<LoadInst>(i);
      const Value *v = li->getPointerOperand();
      Type *type = v->getType();
      
      ref<Expr> base = eval(ki, 0, state).value;
      if (!executeFastReadMemoryOperation(state, base, type, ki))
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
      if (!executeFastWriteMemoryOperation(state, base, value, name))
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
  
Interpreter *Interpreter::createLocal(LLVMContext &ctx, const InterpreterOptions &opts,
                                      InterpreterHandler *ih) {
  return new LocalExecutor(ctx, opts, ih);
}
  
  
  
}

///

