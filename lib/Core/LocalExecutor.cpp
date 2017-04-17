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
  
// static utility functions
  
static std::string getFQFnName(const Function *f) {

  std::string result = f->getParent()->getModuleIdentifier() + "::" + f->getName().str();
  return result;
}
  
LocalExecutor::LocalExecutor(LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih) :
Executor(ctx, opts, ih) {
    
}

LocalExecutor::~LocalExecutor() {
    
    
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
    if (!os->isObjWritten()) {
      ObjectState *newOS = makeSymbolic(state, mo);
      if (countLoadIndirection(type) > 1) {
        // this is a ptr-ptr. allocate something behind the pointer
        Type *subtype = type->getPointerElementType();
        uint64_t size = kmodule->targetData->getTypeStoreSize(subtype);
        size_t align = kmodule->targetData->getPrefTypeAlignment(subtype);
        MemoryObject *newMO = memory->allocate(size, false, true, target->inst, align);
        newMO->setName(mo->name + "*");
        newOS->pointsTo = newMO;
        
        // and constrain this pointer to point at it.
        ref<Expr> exprNewMO = Expr::createPointer((unsigned long) newMO);
        ref<Expr> exprPtr = newOS->read(offsetExpr, width);
        ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(exprPtr, exprNewMO));
        state.addConstraint(eq);
        
      }
    } if (!os->allBytesWritten(offset, bytes)) {
      // some of the bytes to be read were not previously written.
      // they should be made symbolic, but cannot do that without
      // losing prior writes. some form of convert to symbolic
      // while retaining prior writes as constraints
      // if the bytes were previously written, then safe to let the
      // client read its own written data
      klee_error("mixed read/write from single memory object");
    }
  }
  
  ref<Expr> result = os->read(offset, width);
  bindLocal(target, state, result);
  return true;
}
  
bool LocalExecutor::executeFastWriteMemoryOperation(ExecutionState &state,
                                                 ref<Expr> address,
                                                 ref<Expr> value) {
    
  // fast write requires address to be a const expression
  if (!isa<ConstantExpr>(address)) return false;
  ref<ConstantExpr> caddress = cast<ConstantExpr>(address);
    
  Expr::Width type = value->getWidth();
  unsigned bytes = Expr::getMinBytesForWidth(type);
    
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
  if (os->readOnly) {
    terminateStateOnError(state, "memory error: object read only",
                          ReadOnly);
  } else {
    ObjectState *wos = state.addressSpace.getWriteable(mo, os);
    wos->write(offset, value);
    wos->markRangeWritten(offset, bytes);
  }
  return true;
}
  
void LocalExecutor::runFunctionUnconstrained(Function *f) {

  KFunction *kf = kmodule->functionMap[f];
  assert(kf && "failed to get module handle");
  
  ExecutionState *state = new ExecutionState(kf);
  
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
  
ObjectState *LocalExecutor::makeSymbolic(ExecutionState &state,
                                         const MemoryObject *mo) {
  
  // Create a new object state for the memory object (instead of a copy).
  // Find a unique name for this array.  First try the original name,
  // or if that fails try adding a unique identifier.
  unsigned id = 0;
  std::string uniqueName = mo->name;
  while (!state.arrayNames.insert(uniqueName).second) {
    uniqueName = mo->name + "_" + llvm::utostr(++id);
  }
  const Array *array = arrayCache.CreateArray(uniqueName, mo->size);
  ObjectState *os = bindObjectInState(state, mo, mo->isLocal, array);
  state.addSymbolic(mo, array);
  return os;
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
      
      Value *fp = cs.getCalledValue();
      Function *f = getTargetFunction(fp, state);
      KFunction *kf = kmodule->functionMap[f];
      assert(kf && "failed to get module handle");
      
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
      
      ref<Expr> base = eval(ki, 0, state).value;
      if (!executeFastReadMemoryOperation(state, base, v->getType(), ki))
        executeMemoryOperation(state, false, base, 0, ki);
      break;
    }
    case Instruction::Store: {
      ref<Expr> base = eval(ki, 1, state).value;
      ref<Expr> value = eval(ki, 0, state).value;
      if (!executeFastWriteMemoryOperation(state, base, value))
        executeMemoryOperation(state, true, base, value, 0);
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

