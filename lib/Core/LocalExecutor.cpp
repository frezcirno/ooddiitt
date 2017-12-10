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
#include "klee/Internal/System/ProgInfo.h"
#include "klee/SolverStats.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
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

#define countof(a) (sizeof(a)/ sizeof(a[0]))

class bad_expression : public std::runtime_error
{
public:
  bad_expression() : std::runtime_error("null expression") {}
  bad_expression(const char *msg) : std::runtime_error(msg) {}
};


cl::opt<bool>
  AssumeInboundPointers("assume-inbound-pointers",
                        cl::init(true),
                        cl::desc("Assume pointer dereferences are inbounds. (default=on)"));

cl::opt<unsigned>
  LazyAllocationCount("lazy-allocation-count",
                       cl::init(8),
                       cl::desc("Number of items to lazy initialize pointer"));

cl::opt<unsigned>
    LazyAllocationDepth("lazy-allocation-depth",
                        cl::init(2),
                        cl::desc("Depth of items to lazy initialize pointer"));

cl::opt<unsigned>
    MaxLoopIteration("max-loop-iteration",
                      cl::init(1),
                      cl::desc("Number of loop iterations"));

cl::opt<unsigned>
    MaxLoopForks("max-loop-forks",
                  cl::init(16),
                  cl::desc("Number of forks within loop body"));

LocalExecutor::LocalExecutor(LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih,
                             ProgInfo *pi,
                             unsigned tm) :
  Executor(ctx, opts, ih),
  lazyAllocationCount(LazyAllocationCount),
  maxLoopIteration(MaxLoopIteration),
  maxLoopForks(MaxLoopForks),
  maxLazyDepth(LazyAllocationDepth),
  nextLoopSignature(INVALID_LOOP_SIGNATURE),
  progInfo(pi),
  seMaxTime(tm),
  maxStatesInLoop(10000),
  germinalState(nullptr) {
  assert(pi != nullptr);
}

LocalExecutor::~LocalExecutor() {

  delete germinalState;

  if (statsTracker) {
    statsTracker->done();
  }
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

LocalExecutor::ResolveResult LocalExecutor::resolveMO(ExecutionState &state, ref<Expr> address, ObjectPair &op) {

  assert(address.get()->getWidth() == Context::get().getPointerWidth());

  address = state.constraints.simplifyExpr(address);

  if (isa<ConstantExpr>(address)) {
    ref<ConstantExpr> caddress = cast<ConstantExpr>(address);
    if (caddress.get()->isZero()) {
      return ResolveResult::NullAccess;
    }

    // fast path: single in-bounds resolution
    if (state.addressSpace.resolveOne(caddress, op)) {
      return ResolveResult::OK;
    }
    return ResolveResult::NoObject;
  }

  // not a const address, so we have to ask the solver
  solver->setTimeout(coreSolverTimeout);
  bool result = false;
  if (!state.addressSpace.resolveOne(state, solver, address, true, op, result)) {

    ref<ConstantExpr> caddr;
    solver->setTimeout(coreSolverTimeout);
    if (solver->getValue(state, address, caddr)) {
        return resolveMO(state, caddr, op);
    }
  }
  solver->setTimeout(0);
  return result ? ResolveResult::OK : ResolveResult::NoObject;
}

void LocalExecutor::executeAlloc(ExecutionState &state,
                                 unsigned size,
                                 unsigned count,
                                 const llvm::Type *type,
                                 MemKind kind,
                                 KInstruction *target,
                                 bool symbolic) {

  size_t allocationAlignment = getAllocationAlignment(target->inst);
  MemoryObject *mo =
      memory->allocate(size, type, kind, target->inst, allocationAlignment);
  if (!mo) {
    bindLocal(target, state,
              ConstantExpr::alloc(0, Context::get().getPointerWidth()));
  } else {

    mo->name = target->inst->getName();
    mo->count = count;
    ObjectState *os = bindObjectInState(state, mo);
    os->initializeToRandom();
    if (symbolic) {
      makeSymbolic(state, mo);
    }

    bindLocal(target, state, mo->getBaseExpr());
  }
}


void LocalExecutor::executeFree(ExecutionState &state,
                                ref<Expr> address,
                                KInstruction *target) {
  StatePair zeroPointer = fork(state, Expr::createIsZero(address), true);
  if (zeroPointer.first) {
    if (target)
      bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
  }
  if (zeroPointer.second) { // address != 0

    ObjectPair op;
    if (resolveMO(*zeroPointer.second, address, op) == ResolveResult::OK) {

      const MemoryObject *mo = op.first;
      if (mo->isHeap()) {
        zeroPointer.second->addressSpace.unbindObject(mo);
        if (target) {
          bindLocal(target, *zeroPointer.second, Expr::createPointer(0));
        }
      }
    } else {

      // when executing at the function/fragment level, memory objects
      // may not exist. this is not an error.
    }
  }
}

bool LocalExecutor::isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e) {

  Expr::Width width = Context::get().getPointerWidth();
  if (e->getWidth() == width) {

    ref<ConstantExpr> max = Expr::createPointer(width == Expr::Int32 ? UINT32_MAX : UINT64_MAX);
    ref<Expr> eqMax = NotOptimizedExpr::create(EqExpr::create(e, max));

    bool result = false;
    solver->setTimeout(coreSolverTimeout);
    if (solver->mayBeTrue(state, eqMax, result)) {
      solver->setTimeout(0);
      return result;
    }
    solver->setTimeout(0);
  }
  return false;
}

void LocalExecutor::unconstrainGlobals(ExecutionState &state, Function *fn, unsigned counter) {

  Module *m = kmodule->module;
  for (Module::const_global_iterator itr = m->global_begin(), end = m->global_end(); itr != end; ++itr) {
    const GlobalVariable *v = static_cast<const GlobalVariable *>(itr);
    MemoryObject *mo = globalObjects.find(v)->second;

    std::string varName = mo->name;
    if ((!varName.empty()) && (varName.at(0) != '.') && progInfo->isGlobalInput(state.name, varName)) {

      const ObjectState *os = state.addressSpace.findObject(mo);
      ObjectState *wos = state.addressSpace.getWriteable(mo, os);

      WObjectPair wop;
      duplicateSymbolic(state, mo, v, fullName(fn->getName(), counter, varName), wop);

      for (unsigned idx = 0, edx = mo->size; idx < edx; ++idx) {
        wos->write(idx, wop.second->read8(idx));
      }
    }
  }
}

bool LocalExecutor::executeReadMemoryOperation(ExecutionState &state,
                                               ref<Expr> address,
                                               const Type *type,
                                               KInstruction *target) {

  ObjectPair op;
  ResolveResult result = resolveMO(state, address, op);
  if (result != ResolveResult::OK) {
    if (result == ResolveResult::NoObject) {
      // invalid memory read
      errs() << " *** failed to resolve MO on read ***\n";
    }
    terminateState(state);
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
        terminateState(state);
      }
      addConstraint(state, mc);

    } else {
      klee_error("non-optimistic not supported at this time");
    }
    solver->setTimeout(0);
  }

  if (!state.isSymbolic(mo)) {
    if (!isLocallyAllocated(state, mo)) {
      if (mo->kind != klee::MemKind::lazy) {
        outs() << "*** Not converting " << mo->getKindAsStr() << ":" << mo->name << " to symbolic\n";
      } else {
        os = makeSymbolic(state, mo);
      }
    }
  }

  ref<Expr> e = os->read(offsetExpr, width);
  bindLocal(target, state, e);

  if ((countLoadIndirection(type) > 1) && (isUnconstrainedPtr(state, e))) {
    // this is an unconstrained ptr-ptr. this could be either a null ptr or
    // allocate something behind the pointer

    // count current depth of lazy allocations
    unsigned depth = 0;
    for (unsigned end = (unsigned) mo->name.size();
         depth < end && mo->name.at(depth) == '*';
         ++depth);

    ref<ConstantExpr> null = Expr::createPointer(0);
    ref<Expr> eqNull = NotOptimizedExpr::create(EqExpr::create(e, null));

    if (depth >= maxLazyDepth) {

      // too deep. no more forking for this pointer.
      state.addConstraint(eqNull);

    } else {

      StatePair sp = fork(state, eqNull, false);

      // in the true case, ptr is null, so nothing further to do

      // in the false case, allocate new memory for the ptr and
      // constrain the ptr to point to it.
      if (sp.second != nullptr) {

        Type *subtype = type->getPointerElementType()->getPointerElementType();
        MemoryObject *newMO = allocMemory(*sp.second, subtype, target->inst, MemKind::lazy,
                                          '*' + mo->name, 0, lazyAllocationCount);

        bindObjectInState(*sp.second, newMO);

        ref<ConstantExpr> ptr = newMO->getBaseExpr();
        ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(e, ptr));
        sp.second->addConstraint(eq);
      }
    }
  }
  return true;
}

bool LocalExecutor::executeWriteMemoryOperation(ExecutionState &state,
                                                ref<Expr> address,
                                                ref<Expr> value,
                                                const std::string name) {

  ObjectPair op;

  ResolveResult result = resolveMO(state, address, op);
  if (result != ResolveResult::OK) {
    if (result == ResolveResult::NoObject) {
      // invalid memory write
      errs() << " *** failed to resolve MO on write ***\n";
    }
    terminateState(state);
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
  if (mo->name.empty()) {
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
        terminateState(state);
      }
      addConstraint(state, mc);

    } else {
      klee_error("non-optimistic not supported at this time");
    }
    solver->setTimeout(0);
  }
  ObjectState *wos = state.addressSpace.getWriteable(mo, os);
  if (!isa<ConstantExpr>(offsetExpr)) {

    ref<ConstantExpr> cex;
    if (solver->getValue(state, offsetExpr, cex)) {
      ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(offsetExpr, cex));
      addConstraint(state, eq);
      wos->write(cex, value);
    }
  } else {
    wos->write(offsetExpr, value);
  }
  return true;
}

ObjectState *LocalExecutor::makeSymbolic(ExecutionState &state, const MemoryObject *mo) {

  ObjectState *wos = nullptr;
  const ObjectState *os = state.addressSpace.findObject(mo);
  if (os != nullptr) {
    wos = state.addressSpace.getWriteable(mo, os);
    if (state.isSymbolic(mo)) {
      return wos;
    }
  }

  // hold the old object state in memory
  ObjectHolder oh(wos);

  // Create a new object state for the memory object (instead of a copy).
  // Find a unique name for this array.  First try the original name,
  // or if that fails try adding a unique identifier.
  unsigned id = 0;
  std::string uniqueName = mo->name;
  std::string objName = uniqueName;
  while (!state.arrayNames.insert(uniqueName).second) {
    uniqueName = mo->name + "_" + llvm::utostr(++id);
    if (!objName.empty()) {
      errs() << "duplicate obj names: " << objName << ", " << uniqueName << "\n";
    }
  }
  const Array *array = arrayCache.CreateArray(uniqueName, mo->size);

  wos = bindObjectInState(state, mo, array);
  state.addSymbolic(mo, array);
  if (!oh.isNull()) {
    wos->cloneWritten(oh.getOS());
  }
  return wos;
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
  MemoryObject *mo = memory->allocate(size, type, kind, allocSite, align);
  if (mo == nullptr) {
    klee_error("Could not allocate memory for symbolic allocation");
  } else {
    mo->name = name;
    mo->count = count;
  }
  return mo;
}

bool LocalExecutor::allocSymbolic(ExecutionState &state,
                                  Type *type,
                                  const llvm::Value *allocSite,
                                  MemKind kind,
                                  std::string name,
                                  WObjectPair &wop,
                                  size_t align,
                                  unsigned count) {

  wop.first = nullptr;
  wop.second = nullptr;
  MemoryObject *mo = allocMemory(state, type, allocSite, kind, name, align, count);
  if (mo != nullptr) {
    ObjectState *os = makeSymbolic(state, mo);
    wop.first = mo;
    wop.second = os;
    return true;
  }
  return false;
}


bool LocalExecutor::duplicateSymbolic(ExecutionState &state,
                                      const MemoryObject *origMO,
                                      const llvm::Value *allocSite,
                                      std::string name,
                                      WObjectPair &wop) {

  MemoryObject *mo = memory->allocate(origMO->size, origMO->type, origMO->kind, allocSite, origMO->align);
  if (mo == nullptr) {
    klee_error("Could not allocate memory for symbolic duplication");
    return false;
  }
  mo->name = name;
  mo->count = origMO->count;
  ObjectState *os = makeSymbolic(state, mo);
  wop.first = mo;
  wop.second = os;
  return true;
}

bool LocalExecutor::isLocallyAllocated(const ExecutionState &state, const MemoryObject *mo) const {

  const auto &allocas = state.stack.back().allocas;
  return allocas.find(mo) != allocas.end();
}

void LocalExecutor::initializeGlobalValues(ExecutionState &state) {

  for (Module::const_global_iterator itr = kmodule->module->global_begin(),
       end = kmodule->module->global_end();
       itr != end;
       ++itr) {
    const GlobalVariable *v = static_cast<const GlobalVariable *>(itr);
    MemoryObject *mo = globalObjects.find(v)->second;
    std::string name = mo->name;
    if ((name.size() > 0) && (name.at(0) != '.') && progInfo->isGlobalInput(state.name, name)) {
      makeSymbolic(state, mo);
    } else if (v->hasInitializer()) {
      assert(state.isConcrete(mo));
      const ObjectState *os = state.addressSpace.findObject(mo);
      assert(os != nullptr);
      ObjectState *wos = state.addressSpace.getWriteable(mo, os);
      initializeGlobalObject(state, wos, v->getInitializer(), 0);
    }
  }
}

const Module *LocalExecutor::setModule(llvm::Module *module,
                                       const ModuleOptions &opts) {

  assert(kmodule == nullptr);
  const Module *result = Executor::setModule(module, opts);
  kmodule->prepareMarkers();

  // prepare a generic initial state
  germinalState = new ExecutionState();
  germinalState->maxLoopIteration = maxLoopIteration;
  germinalState->lazyAllocationCount = lazyAllocationCount;
  germinalState->maxLazyDepth = maxLazyDepth;
  germinalState->maxLoopForks = maxLoopForks;

  initializeGlobals(*germinalState);
  bindModuleConstants();
  return result;
}

void LocalExecutor::bindModuleConstants() {

  assert(kmodule->constantTable == nullptr);
  kmodule->constantTable = new Cell[kmodule->constants.size()];
  for (unsigned i = 0; i < kmodule->constants.size(); ++i) {
    Cell &c = kmodule->constantTable[i];
    c.value = evalConstant(kmodule->constants[i]);
  }

  for (std::vector<KFunction *>::iterator it = kmodule->functions.begin(),
           ie = kmodule->functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    for (unsigned i = 0; i < kf->numInstructions; ++i) {
      bindInstructionConstants(kf->instructions[i]);
    }
  }
}

void LocalExecutor::runFunctionUnconstrained(Function *f) {

  KFunction *kf = kmodule->functionMap[f];
  if (kf == nullptr) {
    // not in this compilation unit
    return;
  }

  std::string name = f->getName();
  ExecutionState *state = new ExecutionState(*germinalState, kf, name);

  if (pathWriter)
    state->pathOS = pathWriter->open();
  if (symPathWriter)
    state->symPathOS = symPathWriter->open();

  if (statsTracker)
    statsTracker->framePushed(*state, 0);

  initializeGlobalValues(*state);

  // create parameter values
  unsigned index = 0;
  for (Function::const_arg_iterator ai = f->arg_begin(), ae = f->arg_end(); ai != ae; ++ai, ++index) {

    const Argument &arg = *ai;
    std::string argName = arg.getName();
    Type *argType = arg.getType();
    size_t argAlign = arg.getParamAlignment();

    // do not unconstrain ushers
    ref<Expr> e;
    if (isUsherType(argType)) {
      e = Expr::createPointer(0);
    } else {

      // RLR TODO: affirm that this is a fundamental type?
      WObjectPair wop;
      if (!allocSymbolic(*state, argType, &arg, MemKind::param, argName, wop, argAlign)) {
        klee_error("failed to allocate function parameter");
      }
      Expr::Width width = (unsigned) kmodule->targetData->getTypeAllocSizeInBits(argType);
      e = wop.second->read(0, width);
    }
    bindArgument(kf, index, *state, e);
  }

  run(kf, *state);
}

void LocalExecutor::runFunctionAsMain(Function *f,
                                      int argc,
                                      char **argv,
                                      char **envp) {

  assert(false && "calls to runFunctionAsMain deprecated");

#ifdef NEVER

  std::vector<ref<Expr> > arguments;

  // force deterministic initialization of memory objects
//  srand(1);
//  srandom(1);
  
  MemoryObject *argvMO = nullptr;
  KFunction *kf = kmodule->functionMap[f];
  LLVMContext &ctx = kmodule->module->getContext();
  assert(kf && "main not found in this compilation unit");

  std::string name = f->getName();

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
                       Type::getInt8Ty(ctx), MemKind::param, first, 8);
      
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
        memory->allocate(len + 1, Type::getInt8Ty(ctx), MemKind::param, state->pc->inst, 8);
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
  
  run(kf, *state);
  
  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(NULL);

  // clean up global objects
  legalFunctions.clear();
  globalObjects.clear();
  globalAddresses.clear();
  
  if (statsTracker)
    statsTracker->done();

#endif
}
  
void LocalExecutor::run(KFunction *kf, ExecutionState &initialState) {

  outs() << initialState.name << ":\n";
  outs().flush();

  unsigned num_m2m_paths = (unsigned) kf->m2m_paths.size();
  runPaths(kf, initialState, kf->m2m_paths);

  // check to see if a terminated state will cover
  // one of the unreachable m2m blocks
  for (auto state : m2m_pathsTerminatedStates) {
    if (coversUnreachablePath(state, true)) {
      state->endingMarker = state->markers.back();
      interpreterHandler->processTestCase(*state);
      removeCoveredPaths(m2m_pathsUnreachable, state);
    }
    delete state;
  }
  m2m_pathsTerminatedStates.clear();

  if (num_m2m_paths > 0) {
    outs() << "    " << num_m2m_paths - m2m_pathsUnreachable.size();
    outs() << " of " << num_m2m_paths << " m2m paths covered";

    if (m2m_pathsUnreachable.empty()) {
      outs() << "\n";
    } else {
      outs() << ", missing:\n";

      for (const m2m_path_t &path : m2m_pathsUnreachable) {

        bool first = true;
        outs() << "      [";
        for (const unsigned &marker : path) {
          if (!first) outs() << ", ";
          first = false;
          outs() << marker;
        }
        outs() << "]\n";
      }
    }
  }
  outs().flush();
}

void LocalExecutor::markUnreachable(const std::vector<unsigned> &ids) {

  // remove any m2m-paths starting with an id for startBB
  for (unsigned id : ids) {

    // consider each remaining path
    for (auto itr = m2m_pathsRemaining.cbegin(), end = m2m_pathsRemaining.cend(); itr != end; ) {

      assert(!itr->empty());
      if (id == itr->front() % 1000) {
        m2m_pathsUnreachable.insert(*itr);
        itr = m2m_pathsRemaining.erase(itr);
      } else {
        ++itr;
      }
    }
  }
}

void LocalExecutor::runPaths(KFunction *kf, ExecutionState &initialState, m2m_paths_t &paths) {


  // Delay init till now so that ticks don't accrue during
  // optimization and such.
  initTimers();

  m2m_pathsRemaining = paths;
  m2m_pathsUnreachable.clear();
  m2m_pathsCoveredByTerminated.clear();
  BasicBlocks priorStartingBBs;

  while (!m2m_pathsRemaining.empty() && !haltExecution) {

    // select starting bb at head of a remaining path
    // closest to fn entry
    std::set<const BasicBlock*> heads;
    for (const m2m_path_t &path : m2m_pathsRemaining) {
      heads.insert(kf->mapBBlocks[path.front() % 1000]);
    }

    unsigned closest = UINT_MAX;
    const BasicBlock *startBB = nullptr;
    for (const BasicBlock* bb : heads) {
      unsigned distance = kf->getBBIndex(bb);
      if (distance < closest) {
        startBB = bb;
        closest = distance;
      }
    }

    const BasicBlock *adj_startBB = startBB;
      // already started from this BB once before

    std::deque<const BasicBlock*> worklist;
    while (adj_startBB != nullptr && (priorStartingBBs.count(adj_startBB) > 0)) {

      BasicBlocks preds;
      kf->getPredecessorBBs(adj_startBB, preds);
      for (const BasicBlock *pred : preds) {
        worklist.push_back(pred);
      }

      if (!worklist.empty()) {
        adj_startBB = worklist.front();
        worklist.pop_front();
      } else {
        adj_startBB = nullptr;
      }
    }

    if (adj_startBB != nullptr) {
      outs() << "  Starting from: ";
      if (adj_startBB == &kf->function->getEntryBlock()) {
        outs() << "entry\n";
      } else {
        outs() << kf->mapMarkers[adj_startBB].front() << "\n";
      }
      priorStartingBBs.insert(adj_startBB);
      if (runFrom(kf, initialState, adj_startBB) != HaltReason::InvalidExpr) {

        // ok or timeout.  in either case,
        // paths starting at startBB are unreachable.
        // remove any m2m-paths starting with an id for startBB
        markUnreachable(kf->mapMarkers[startBB]);
      }
    } else {
      // unable to find an alternative starting point for startBB
      // therefore, these paths must be unreachable
      markUnreachable(kf->mapMarkers[startBB]);
    }
  }
}

LocalExecutor::HaltReason LocalExecutor::runFrom(KFunction *kf, ExecutionState &initial, const BasicBlock *start) {

  const uint64_t stats_granularity = 1000;
  uint64_t stats_counter = stats_granularity;

  // set new initial program counter
  ExecutionState *initState = new ExecutionState(initial);

  unsigned entry = kf->basicBlockEntry[const_cast<BasicBlock*>(start)];
  initState->pc = &kf->instructions[entry];

  if (start != &kf->function->getEntryBlock()) {

    // record starting marker
    initState->startingMarker = kf->mapMarkers[start].front();

    // declare local variables symbolic
    prepareLocalSymbolics(kf, *initState);

    // if jumping into the interior of a loop, push required loop frames
    std::vector<const BasicBlock*> hdrs;
    kf->findContainingLoops(start, hdrs);

    // create loop frames in order
    StackFrame &sf = initState->stack.back();
    for (auto itr = hdrs.begin(), end = hdrs.end(); itr != end; ++itr) {
      sf.loopFrames.push_back(LoopFrame(*itr, getNextLoopSignature()));
    }
  }

  processTree = new PTree(initState);
  initState->ptreeNode = processTree->root;

  states.insert(initState);
  searcher = constructUserSearcher(*this, Searcher::CoreSearchType::BFS);
  std::vector<ExecutionState *> newStates(states.begin(), states.end());
  searcher->update(nullptr, newStates, std::vector<ExecutionState *>());

  struct timespec tm;
  clock_gettime(CLOCK_MONOTONIC, &tm);
  uint64_t startTime = (uint64_t) tm.tv_sec;
  uint64_t stopTime = seMaxTime == 0 ? UINT64_MAX : startTime + seMaxTime;
  HaltReason halt = HaltReason::OK;

  while (!states.empty() && !m2m_pathsRemaining.empty() && !haltExecution && (halt == HaltReason::OK)) {
    ExecutionState &state = searcher->selectState();

    KInstruction *ki = state.pc;
    stepInstruction(state);
    try {
      executeInstruction(state, ki);
    } catch (bad_expression &e) {
      halt = HaltReason::InvalidExpr;
      errs() << "    * uninitialized expression, halting execution\n";
    }

    processTimers(&state, 0);
    updateStates(&state);

    if (--stats_counter == 0) {
      stats_counter = stats_granularity;

      // check for exceeding maximum time
      clock_gettime(CLOCK_MONOTONIC, &tm);
      if ((uint64_t) tm.tv_sec > stopTime) {
        errs() << "    * max time elapsed, halting execution\n";
        halt = HaltReason::TimeOut;
      }
      checkMemoryUsage(kf);
    } else {
      checkMemoryUsage();
    }
  }

  forkCounter.clear();
  for (ExecutionState *state : states) {
    terminateState(*state);
  }
  updateStates(nullptr);
  assert(states.empty());

  delete searcher;
  searcher = nullptr;

  delete processTree;
  processTree = nullptr;

  return halt;
}


void LocalExecutor::terminateState(ExecutionState &state) {

  if (!state.isProcessed) {
    // did not generate a test case.  if it covers an remaining path
    // save it for possible generation later

    const m2m_path_t &trace = state.markers;
    unsigned trace_length = (unsigned) trace.size();
    for (const auto &path : m2m_pathsRemaining) {
      auto found = std::search(trace.begin(), trace.end(), path.begin(), path.end());
      if (found != trace.end()) {
        unsigned path_length = (unsigned) path.size();
        unsigned offset = (unsigned) (found - trace.begin());
        if (trace_length - offset > path_length) {

          // this state did cover past an remained path
          if (m2m_pathsCoveredByTerminated.count(path) == 0) {
            m2m_pathsCoveredByTerminated.insert(path);
            m2m_pathsTerminatedStates.insert(new ExecutionState(state));
          }
        }
      }
    }
  }

  Executor::terminateState(state);
}

void LocalExecutor::checkMemoryUsage(KFunction *kf) {

  Executor::checkMemoryUsage();

  if (kf != nullptr) {
    for (const auto pair : kf->loopInfo) {
      const BasicBlock *hdr = pair.first;
      unsigned num = numStatesInLoop(hdr);
      if (num > maxStatesInLoop) {
        termStatesInLoop(hdr);
        outs() << "terminated " << num << " states in loop: " << kf->mapMarkers[hdr].front() << "\n";
      }
    }
  }
}

void LocalExecutor::termStatesInLoop(const BasicBlock *hdr) {

  for (ExecutionState *state : states) {
    if (!state->stack.empty()) {
      const StackFrame &sf = state->stack.back();
      if (!sf.loopFrames.empty()) {
        const LoopFrame &lf = sf.loopFrames.back();
        if (lf.hdr == hdr) {
          terminateState(*state);
        }
      }
    }
  }
}


unsigned LocalExecutor::numStatesInLoop(const BasicBlock *hdr) const {

  unsigned counter = 0;
  for (const ExecutionState *state : states) {
    if (!state->stack.empty()) {
      const StackFrame &sf = state->stack.back();
      if (!sf.loopFrames.empty()) {
        const LoopFrame &lf = sf.loopFrames.back();
        if (lf.hdr == hdr) {
          ++counter;
        }
      }
    }
  }
  return counter;
}

unsigned LocalExecutor::numStatesWithLoopSig(unsigned loopSig) const {

  unsigned counter = 0;
  for (const ExecutionState *state : states) {
    if (!state->stack.empty()) {
      const StackFrame &sf = state->stack.back();
      if (!sf.loopFrames.empty()) {
        const LoopFrame &lf = sf.loopFrames.back();
        if (lf.loopSignature == loopSig) {
          ++counter;
        }
      }
    }
  }
  return counter;
}

void LocalExecutor::removeCoveredPaths(m2m_paths_t &paths, const ExecutionState *state) {

  const m2m_path_t &trace = state->markers;
  for (auto itr = paths.begin(), end = paths.end(); itr != end;) {
    const m2m_path_t &path = *itr;
    auto found = std::search(trace.begin(), trace.end(), path.begin(), path.end());
    if (found == trace.end()) {
      ++itr;
    } else {
      itr = paths.erase(itr);
    }
  }
}


void LocalExecutor::updateStates(ExecutionState *current) {

  for (auto state : removedStates) {
    if (state->isProcessed) {
      removeCoveredPaths(m2m_pathsRemaining, state);
    }
  }
  Executor::updateStates(current);
}

bool LocalExecutor::coversPath(const m2m_paths_t &paths, const ExecutionState *state, bool extends) const {

  const m2m_path_t &trace = state->markers;
  unsigned trace_length = (unsigned) trace.size();
  for (const auto &path : paths) {
    auto found = std::search(trace.begin(), trace.end(), path.begin(), path.end());
    if (found != trace.end()) {
      if (extends) {
        unsigned path_length = (unsigned) path.size();
        unsigned offset = (unsigned) (found - trace.begin());
        if (trace_length - offset > path_length) {
          return true;
        }
      } else {

        // matches a remaining path, so keep the test case
        return true;
      }
    }
  }
  return false;
}

bool LocalExecutor::generateTestCase(const ExecutionState &state) const {
  return coversRemainingPath(&state, false) || coversUnreachablePath(&state, true);
}

ref<ConstantExpr> LocalExecutor::ensureUnique(ExecutionState &state, const ref<Expr> &e) {

  ref<ConstantExpr> result;

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e)) {
    result = CE;
  } else {

    solver->setTimeout(coreSolverTimeout);
    if (solver->getValue(state, e, result)) {

      bool isTrue;
      if (solver->mustBeTrue(state, EqExpr::create(e, result), isTrue)) {
        if (!isTrue) {
          state.addConstraint(NotOptimizedExpr::create(EqExpr::create(e, result)));
        }
      } else {
        klee_error("solver failure");
      }
    } else {
      klee_error("solver failure");
    }
    solver->setTimeout(0);
  }

  return result;
}

bool LocalExecutor::isUnique(const ExecutionState &state, ref<Expr> &e) const {

  bool result = false;
  if (isa<ConstantExpr>(e)) {
    result = true;
  } else {

    ref<ConstantExpr> value;
    solver->setTimeout(coreSolverTimeout);
    if (solver->getValue(state, e, value)) {

      bool isTrue = false;
      if (solver->mustBeTrue(state, EqExpr::create(e, value), isTrue)) {
        result = isTrue;
      }
    }
    solver->setTimeout(0);
  }
  return result;
}


void LocalExecutor::transferToBasicBlock(llvm::BasicBlock *dst, llvm::BasicBlock *src, ExecutionState &state) {

  // if src and dst bbs have the same parent, then this is a branch
  // update the loop frame
  if (dst->getParent() == src->getParent()) {
    StackFrame &sf = state.stack.back();
    KFunction *kf = sf.kf;

    if (kf->isLoopHeader(dst)) {
      if (kf->isInLoop(dst, src)) {

        // completed a cycle
        assert(!sf.loopFrames.empty() && "cycled an empty loop");
        ++sf.loopFrames.back().counter;

      } else {
        // this is a new loop
        sf.loopFrames.push_back(LoopFrame(dst, getNextLoopSignature()));
      }
    } else if (!sf.loopFrames.empty()) {

      LoopFrame *lf = &sf.loopFrames.back();
      const BasicBlock *hdr = lf->hdr;
      if (!kf->isInLoop(hdr, dst)) {

        // just left the loop
        sf.loopFrames.pop_back();
      }
    }
  }
  Executor::transferToBasicBlock(dst, src, state);
}

bool LocalExecutor::isUsherType(const llvm::Type *type) const {

  if (type->isPointerTy()) {
    Type *sub_type = type->getPointerElementType();
    if (sub_type->isStructTy()) {
      if (sub_type->getStructName() == "struct._usher_t") {
        return true;
      }
    }
  }
  return false;
}

void LocalExecutor::prepareLocalSymbolics(KFunction *kf, ExecutionState &state) {

  // iterate over the entry block and execute allocas
  Function *fn = kf->function;
  if (fn->size() > 0) {

    unsigned numArgs = fn->arg_size();
    KInstIterator pc = kf->instructions;
    const Instruction *end = fn->getEntryBlock().getTerminator();
    const Instruction *cur = nullptr;
    while (cur != end) {
      KInstruction *ki = pc;
      ++pc;
      cur = ki->inst;
      if (const AllocaInst *ai = dyn_cast<AllocaInst>(cur)) {
        Type *alloc_type = ai->getAllocatedType();
        unsigned size = (unsigned) kmodule->targetData->getTypeStoreSize(alloc_type);
        if (ai->isArrayAllocation()) {
          assert("resolve array allocation");
        }

        bool to_symbolic = !(isUsherType(alloc_type) || ki->inst->getName().empty());
        executeAlloc(state, size, 1, ai->getAllocatedType(), MemKind::alloca, ki, to_symbolic);

      } else if (const StoreInst *si = dyn_cast<StoreInst>(cur)) {

        // the first numArg store operations setup the arguments
        if (numArgs > 0) {
          const Value *v = si->getValueOperand();
          assert(v->hasName());
          ref<Expr> base = eval(ki, 1, state).value;
          ref<Expr> value = eval(ki, 0, state).value;
          executeWriteMemoryOperation(state, base, value, v->getName());
          --numArgs;
        }
      }
    }
  }
}

void LocalExecutor::executeInstruction(ExecutionState &state, KInstruction *ki) {
  Instruction *i = ki->inst;
  switch (i->getOpcode()) {
      // Control flow

    case Instruction::PHI: {
      if (state.incomingBBIndex == INVALID_BB_INDEX) {
        throw bad_expression();
      }
      Executor::executeInstruction(state, ki);
      break;
    }

    case Instruction::Br: {
      BranchInst *bi = cast<BranchInst>(i);
      BasicBlock *src = i->getParent();
      KFunction *kf = state.stack.back().kf;

      if (bi->isUnconditional()) {
        BasicBlock *dst = bi->getSuccessor(0);
        transferToBasicBlock(dst, src, state);

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

        ExecutionState *states[2] = { branches.first, branches.second };
        bool bothSatisfyable = (states[0] != nullptr) && (states[1] != nullptr);

        for (unsigned index = 0; index < countof(states); ++index) {
          if (states[index] != nullptr) {
            BasicBlock *dst = bi->getSuccessor(index);
            transferToBasicBlock(dst, src, *states[index]);

            if (bothSatisfyable) {
              StackFrame &sf = states[index]->stack.back();
              if (!sf.loopFrames.empty()) {
                LoopFrame &lf = sf.loopFrames.back();
                ++forkCounter[lf.hdr];
                if (kf->isLoopExit(lf.hdr, src) && kf->isInLoop(lf.hdr, dst)) {

                  if (lf.counter > maxLoopIteration && forkCounter[lf.hdr] > maxLoopForks){

                    // finally consider terminating the state.
                    terminateState(*states[index]);
                  }
                }
              }
            }
          }
        }
      }
      break;
    }

    case Instruction::Invoke:
    case Instruction::Call: {

      const CallSite cs(i);
      Function *fn = getTargetFunction(cs.getCalledValue(), state);
      std::string fnName = fn->getName();

      // if this function does not return, (exit, abort, zopc_exit, etc)
      // then this state has completed
      if (fn->hasFnAttribute(Attribute::NoReturn) || fnName == "zopc_exit") {
        terminateStateOnExit(state);
        return;
      }

      // if this is a special function, let
      // the standard executor handle it
      if (specialFunctionHandler->isSpecial(fn)) {
        Executor::executeInstruction(state, ki);
        return;
      }

      // if this is a call to mark(), then log the marker to state
      if (((fnName == "MARK") || (fnName == "mark")) &&
          (fn->arg_size() == 2) &&
          (fn->getReturnType()->isVoidTy())) {

        const Constant *arg0 = dyn_cast<Constant>(cs.getArgument(0));
        const Constant *arg1 = dyn_cast<Constant>(cs.getArgument(1));
        if ((arg0 != nullptr) && (arg1 != nullptr)) {
          unsigned fnID = (unsigned) arg0->getUniqueInteger().getZExtValue();
          unsigned bbID = (unsigned) arg1->getUniqueInteger().getZExtValue();

          state.addMarker(fnID, bbID);
          return;
        }
      }

      // if this is a call to guide, just return 2nd argument
      if ((fnName == "guide" && (cs.arg_size() == 2))) {
        ref<Expr> retExpr = eval(ki, 2, state).value;
        bindLocal(ki, state, retExpr);
        return;
      }

      // hence, this is a function in this module
      unsigned counter = state.callTargetCounter[fnName]++;

      // consider the arguments pushed for the call, rather than
      // args expected by the target
      unsigned numArgs = cs.arg_size();
      for (unsigned index = 0; index < numArgs; ++index) {
        const Value *v = cs.getArgument(index);
        Type *argType = v->getType();

        if ((countLoadIndirection(argType) > 0) &&
            !progInfo->isConstParam(fnName, index)) {

          // do not unconstrain ushers
          if (isUsherType(argType)) {
            continue;
          }

          ref<ConstantExpr> address = ensureUnique(state, eval(ki, index + 1, state).value);
          Expr::Width width = address->getWidth();
          assert(width == Context::get().getPointerWidth());

          ObjectPair op;
          if (resolveMO(state, address, op) == ResolveResult::OK) {
            const MemoryObject *orgMO = op.first;
            const ObjectState *orgOS = op.second;
            ObjectState *argOS = state.addressSpace.getWriteable(orgMO, orgOS);

            Type *eleType = argType->getPointerElementType();
            unsigned eleSize = (unsigned) kmodule->targetData->getTypeAllocSize(eleType);
            unsigned offset = (unsigned) (address->getZExtValue() - orgMO->address);
            unsigned count = (orgMO->size - offset) / eleSize;

            // unconstrain from address to end of the memory block
            WObjectPair wop;
            if (!allocSymbolic(state,
                               eleType,
                               v,
                               MemKind::output,
                               fullName(fnName, counter, std::to_string(index + 1)),
                               wop,
                               0,
                               count)) {
              klee_error("failed to allocate ptr argument");
            }

            ObjectState *newOS = wop.second;
            for (unsigned idx = 0, end = count * eleSize; idx < end; ++idx) {
              argOS->write8(offset + idx, newOS->read8(idx));
            }
          } else {
//            assert(false && "failed to resolve a parameter");
          }
        }
      }

      // unconstrain global variables
      unconstrainGlobals(state, fn, counter);

      // now get the return type
      Type *ty = fn->getReturnType();
      if (!ty->isVoidTy()) {

        WObjectPair wop;
        if (!allocSymbolic(state, ty, i, MemKind::output, fullName(fnName, counter, "0"), wop)) {
          klee_error("failed to allocate called function parameter");
        }
        Expr::Width width = (unsigned) kmodule->targetData->getTypeAllocSizeInBits(ty);
        ref<Expr> retExpr = wop.second->read(0, width);
        bindLocal(ki, state, retExpr);

        // need return value lazy init to occur here, otherwise, the allocation
        // gets the wrong name.
        if (ty->isPointerTy()) {

          // two possible returns for a pointer type, nullptr and a valid object

          ref<ConstantExpr> null = Expr::createPointer(0);
          ref<Expr> eqNull = NotOptimizedExpr::create(EqExpr::create(retExpr, null));
          StatePair sp = fork(state, eqNull, false);

          // in the true case, ptr is null, so nothing further to do

          // in the false case, allocate new memory for the ptr and
          // constrain the ptr to point to it.
          if (sp.second != nullptr) {

            MemKind kind = MemKind::lazy;
            unsigned count = lazyAllocationCount;

            // special handling for zopc_malloc. argument contains the allocation size
            if (fnName == "zopc_malloc") {
              kind = MemKind::heap;
              ref<Expr> size = eval(ki, numArgs, *sp.second).value;
              size = sp.second->constraints.simplifyExpr(size);

              if (ConstantExpr *CE = dyn_cast<ConstantExpr>(size)) {
                count = (unsigned) CE->getZExtValue();
              } else {

                // select a smallest size that might be true
                Expr::Width w = size->getWidth();
                ref<ConstantExpr> min_size;
                bool result = false;
                for (unsigned try_size = 16; !result && try_size <= 64536; try_size *= 2) {
                  min_size = ConstantExpr::create(try_size, w);
                  bool success = solver->mayBeTrue(state, UltExpr::create(size, min_size), result);
                  assert(success && "FIXME: Unhandled solver failure");
                }
                if (result) {
                  sp.second->addConstraint(UltExpr::create(size, min_size));
                  bool success = solver->getValue(*sp.second, size, min_size);
                  assert(success && "FIXME: solver just said mayBeTrue");
                  sp.second->addConstraint(NotOptimizedExpr::create(EqExpr::create(size, min_size)));
                  count = (unsigned) min_size->getZExtValue();
                } else {
                  // too big of an allocation
                  terminateState(*sp.second);
                  return;
                }
              }
            }
            Type *subtype = ty->getPointerElementType();

            MemoryObject *newMO = allocMemory(*sp.second, subtype, i, kind, fullName(fnName, counter, "*0"), 0, count);
            bindObjectInState(*sp.second, newMO);

            ref<ConstantExpr> ptr = newMO->getBaseExpr();
            sp.second->addConstraint(NotOptimizedExpr::create(EqExpr::create(retExpr, ptr)));
          }
        }
      }
      break;
    }

    // Memory instructions...
      
    case Instruction::Alloca: {
      AllocaInst *ai = cast<AllocaInst>(i);

      unsigned size = (unsigned) kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
      if (ai->isArrayAllocation()) {
        assert("resolve array allocation");
      }

      executeAlloc(state, size, 1, ai->getAllocatedType(), MemKind::alloca, ki);
      break;
    }

    case Instruction::GetElementPtr: {
      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
      ref<Expr> base = eval(ki, 0, state).value;

      ObjectPair op;
      ResolveResult result = resolveMO(state, base, op);
      if (result == ResolveResult::OK) {
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
          if (!(solver->mayBeTrue(state, mc, inBounds) && inBounds)) {
            solver->setTimeout(0);
            state.pc = state.prevPC;
            terminateState(state);
          } else {
            addConstraint(state, mc);
          }
        } else {
          klee_error("non-optimistic not supported at this time");
        }
        solver->setTimeout(0);
        bindLocal(ki, state, base);
      } else {

        // invalid memory access
        if (result == ResolveResult::NoObject) {
          errs() << " *** failed to resolve MO on GEP ***\n";
        }
        terminateState(state);
      }
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


void LocalExecutor::InspectSymbolicSolutions(const ExecutionState *state) {

  std::vector<SymbolicSolution> out;
  bool success = Executor::getSymbolicSolution(*state, out);
  if (success) {

    for (auto itrObj = out.begin(), endObj = out.end(); itrObj != endObj; ++itrObj) {

      auto &sym = *itrObj;
      assert(sym.first->type != nullptr);

      std::string name = sym.first->name;
      const llvm::Type *type = sym.first->type;
      std::vector<unsigned char> &data = sym.second;
      (void) type;
      (void) data;

      // scale to 32 or 64 bits
      unsigned ptr_width = (Context::get().getPointerWidth() / 8);
      std::vector<unsigned char> addr;
      unsigned char *addrBytes = ((unsigned char *) &(sym.first->address));
      for (unsigned index = 0; index < ptr_width; ++index, ++addrBytes) {
        addr.push_back(*addrBytes);
      }
    }
  }
}


const Cell& LocalExecutor::eval(KInstruction *ki, unsigned index, ExecutionState &state) const {

  const Cell& result = Executor::eval(ki, index, state);
  if (result.value.isNull()) {
    throw bad_expression();
  }
  return result;
}


unsigned LocalExecutor::countLoadIndirection(const llvm::Type* type) const {

  unsigned counter = 0;

  while (type->isPointerTy()) {
    type = type->getPointerElementType();
    ++counter;
  }
  return counter;
}
  
Interpreter *Interpreter::createLocal(LLVMContext &ctx,
                                      const InterpreterOptions &opts,
                                      InterpreterHandler *ih,
                                      ProgInfo *progInfo,
                                      unsigned seMaxTime) {
  return new LocalExecutor(ctx, opts, ih, progInfo, seMaxTime);
}

  
}

///

