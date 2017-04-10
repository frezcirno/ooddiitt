//===-- LocalExecutor.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "LocalExecutor.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "StatsTracker.h"
#include "PTree.h"

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

using namespace llvm;

namespace klee {
  
LocalExecutor::LocalExecutor(LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih) :
Executor(ctx, opts, ih) {
    
}

LocalExecutor::~LocalExecutor() {
    
    
}

void LocalExecutor::executeMemoryOperation(ExecutionState &state,
                                        bool isWrite,
                                        ref<Expr> address,
                                        ref<Expr> value /* undef if read */,
                                        KInstruction *target /* undef if write */) {
    
  if (isWrite) {
    if (executeFastWriteMemoryOperation(state, address, value)) return;
  } else {
    if (executeFastReadMemoryOperation(state, address, target)) return;
  }
  Executor::executeMemoryOperation(state, isWrite, address, value, target);
}
  
bool LocalExecutor::executeFastReadMemoryOperation(ExecutionState &state,
                                                  ref<Expr> address,
                                                  KInstruction *target) {
    
  // fast read requires address to be a const expression
  if (!isa<ConstantExpr>(address)) return false;
  ref<ConstantExpr> caddress = cast<ConstantExpr>(address);
  
  Expr::Width type = getWidthForLLVMType(target->inst->getType());
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
    
  ref<Expr> result = os->read(offset, type);
    
  if (interpreterOpts.MakeConcreteSymbolic) {
    result = replaceReadWithSymbolic(state, result);
  }
    
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
    if ((argAlign == 0) && argType->isSized()) {
      
      // no align for this arg, get a preference for the type
      argAlign = kmodule->targetData->getPrefTypeAlignment(argType);
    }
    
    // if all else fails, 8 is one of our favorite numbers
    if (argAlign == 0) {
      argAlign = 8;
    }
    
    MemoryObject *mo = memory->allocate(argSize, false, true, arg, argAlign);
    
    if (mo == nullptr) {
      klee_error("Could not allocate memory for function arguments");
    }
    
    bindArgument(kf, index, *state, mo->getBaseExpr());
    executeMakeSymbolic(*state, mo, argName);
    
    errs() << argName;
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
  
  
  
Interpreter *Interpreter::createLocal(LLVMContext &ctx, const InterpreterOptions &opts,
                                      InterpreterHandler *ih) {
  return new LocalExecutor(ctx, opts, ih);
}
  
}

///

