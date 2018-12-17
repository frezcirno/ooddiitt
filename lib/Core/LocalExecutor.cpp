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
#include "klee/Internal/System/debugbreak.h"

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
  VerifyConstraints("verify-constraints",
                    cl::init(false),
                    cl::desc("Perform additional constraint verification before adding"));

cl::opt<unsigned>
  LazyAllocationCount("lazy-allocation-count",
                       cl::init(8),
                       cl::desc("Number of items to lazy initialize pointer"));

cl::opt<unsigned>
  MinLazyAllocationSize("min-lazy-allocation-size",
                        cl::init(0x400),
                        cl::desc("minimum size of a lazy allocation"));

cl::opt<unsigned>
    LazyAllocationDepth("lazy-allocation-depth",
                        cl::init(4),
                        cl::desc("Depth of items to lazy initialize pointer"));

cl::opt<bool>
    LazyAllocationExt("lazy-allocation-ext",
                        cl::init(true),
                        cl::desc("extend lazy allocation to include existing memory objects of same type"));

cl::opt<unsigned>
    MaxLoopIteration("max-loop-iteration",
                      cl::init(1),
                      cl::desc("Number of loop iterations"));

cl::opt<unsigned>
    MaxLoopForks("max-loop-forks",
                  cl::init(16),
                  cl::desc("Number of forks within loop body"));

cl::opt<unsigned>
    DebugValue("debug-value",
                cl::init(0),
                cl::desc("context specific debug value"));

LocalExecutor::LocalExecutor(LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih) :
  Executor(ctx, opts, ih),
  lazyAllocationCount(LazyAllocationCount),
  maxLoopIteration(MaxLoopIteration),
  maxLoopForks(MaxLoopForks),
  maxLazyDepth(LazyAllocationDepth),
  nextLoopSignature(INVALID_LOOP_SIGNATURE),
  progInfo(opts.pinfo),
  maxStatesInLoop(10000),
  germinalState(nullptr),
  heap_base(opts.heap_base),
  progression(opts.progression),
  verbose(opts.verbose),
  terminatedPendingState(false)  {

  memory->setBaseAddr(heap_base);
  tsolver = new TimedSolver(solver, coreSolverTimeout);
  switch (opts.mode) {
    case ExecModeID::zop:
      doSaveComplete = true;
      doSaveFault = false;
      doAssumeInBounds = true;
      doLocalCoverage = true;
      break;
    case ExecModeID::fault:
      doSaveComplete = false;
      doSaveFault = true;
      doAssumeInBounds = false;
      doLocalCoverage = false;
      break;
    default:
      klee_error("invalid execution mode");
  }

  Executor::setVerifyContraints(VerifyConstraints);
}

LocalExecutor::~LocalExecutor() {

  delete tsolver;
  tsolver = nullptr;

  if (germinalState != nullptr) {
    // this last state is leaked.  something in solver
    // tear-down does not like its deletion
    germinalState = nullptr;
  }

  if (statsTracker) {
    statsTracker->done();
  }
}

bool LocalExecutor::addConstraintOrTerminate(ExecutionState &state, ref<Expr> e) {

  if (VerifyConstraints) {
    std::vector<SymbolicSolution> in;
    getSymbolicSolution(state, in);
  }

  bool result = false;
  if (tsolver->mayBeTrue(state, e, result) && result) {
    addConstraint(state, e);

    if (VerifyConstraints) {
      std::vector<SymbolicSolution> out;
      getSymbolicSolution(state, out);
    }

    return true;
  }
  terminateState(state);
  return false;
}

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
    if (tsolver->getValue(state, address, caddr)) {
      return resolveMO(state, caddr, op);
    }
  }
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

    e = state.constraints.simplifyExpr(e);

    // ensure this is a simple expression, i.e. only concats of constant reads in the tree of subexprs
    bool simple = true;
    std::deque<ref<Expr> > worklist = {e};
    while (simple && !worklist.empty()) {
      ref<Expr> child = worklist.front();
      worklist.pop_front();
      Expr::Kind k = child->getKind();
      if (k == Expr::Kind::Concat) {
        for (unsigned idx = 0, end = child->getNumKids(); idx < end; ++idx) {
          worklist.push_back(child->getKid(idx));
        }
      } else if (k == Expr::Kind::Read) {
        if ((child->getNumKids() != 1) || (child->getKid(0)->getKind() != Expr::Kind::Constant)) {
          simple = false;
        }
      } else {
        simple = false;
      }
    }

    if (simple) {
      ref<ConstantExpr> max = Expr::createPointer(width == Expr::Int32 ? UINT32_MAX : UINT64_MAX);
      ref<Expr> eqMax = EqExpr::create(e, max);

      bool result = false;
      return tsolver->mayBeTrue(state, eqMax, result) && result;
    }
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

      std::string fnName = "unknown";
      bool unconstrain = false;
      if (fn != nullptr) {
        fnName = fn->getName().str();
        unconstrain = progInfo->isReachableOutput(fnName, varName);
      } else {
        fnName = "still_unknown";
        unconstrain = true;
      }

      if (unconstrain) {
        const ObjectState *os = state.addressSpace.findObject(mo);
        ObjectState *wos = state.addressSpace.getWriteable(mo, os);

        WObjectPair wop;
        duplicateSymbolic(state, mo, v, fullName(fnName, counter, varName), wop);

        for (unsigned idx = 0, edx = mo->size; idx < edx; ++idx) {
          wos->write(idx, wop.second->read8(idx));
        }
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
    terminateStateOnFault(state, target, "read resolveMO");
    return false;
  }

  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  Expr::Width width = getWidthForLLVMType(target->inst->getType());
  unsigned bytes = Expr::getMinBytesForWidth(width);

  // target state may change during this call, so use indirect access
  ExecutionState *currState = &state;

  ref<Expr> offsetExpr = mo->getOffsetExpr(address);
  if (isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> coffsetExpr = cast<ConstantExpr>(offsetExpr);
    const auto offset = (unsigned) coffsetExpr->getZExtValue();
    if (offset + bytes > os->visible_size) {
      terminateStateOnFault(*currState, target, "read OoB const offset");
      return false;
    }
  } else {

    ref<Expr> mc = os->getBoundsCheckOffset(offsetExpr, bytes);

    // at most one of these forks will survive
    // currState will point to the sole survivor
    // and will be constrained to bounds.
    Executor::StatePair sp = fork(*currState, mc, true);
    if (sp.first == nullptr) {
      // no satisfying inbounds solution, both currState and sp.second must terminate
      terminateStateOnFault(*currState, target, "read OoB1 offset");
      if (sp.second != nullptr && sp.second != currState) {
        terminateStateOnFault(*sp.second, target, "read OoB2 offset");
      }
      return false;

    } else {
      // inbound solution exists.  should continue as currState. sp.second must terminate
      currState = sp.first;
      if (sp.second != nullptr) {
        terminateStateOnFault(*sp.second, target, "read OoB3 offset");
      }
    }
  }

  if (!currState->isSymbolic(mo)) {
    if (!isLocallyAllocated(*currState, mo)) {
      if (mo->kind == klee::MemKind::lazy) {
        os = makeSymbolic(*currState, mo);
      }
    }
  }

  ref<Expr> e = os->read(offsetExpr, width);
  bindLocal(target, *currState, e);

  if ((countLoadIndirection(type) > 1) && (isUnconstrainedPtr(*currState, e))) {
    // this is an unconstrained ptr-ptr. this could be either a null ptr or
    // allocate something behind the pointer

    // count current depth of lazy allocations
    unsigned depth = 0;
    for (auto end = (unsigned) mo->name.size(); depth < end && mo->name.at(depth) == '*'; ++depth);

    ref<ConstantExpr> null = Expr::createPointer(0);
    ref<Expr> eqNull = EqExpr::create(e, null);

    if (depth >= maxLazyDepth) {

      // too deep. no more forking for this pointer.
      addConstraintOrTerminate(*currState, eqNull);

    } else {

      StatePair sp = fork(*currState, eqNull, true);

      // in the true case, ptr is null, so nothing further to do

      // in the false case, allocate new memory for the ptr and
      // constrain the ptr to point to it.
      if (sp.second != nullptr) {

        // pointer may not be null
        std::vector<ObjectPair> listOPs;
        Type *subtype = type->getPointerElementType()->getPointerElementType();

#if 0 == 1
        // this is just for debugging and diagnostics
        std::string type_desc;
        llvm::raw_string_ostream rso(type_desc);
        subtype->print(rso);
        type_desc = rso.str();
#endif

        if (subtype->isFirstClassType()) {

          if (LazyAllocationExt) {

            // consider any existing objects in memory of the same type
            sp.second->addressSpace.getMemoryObjects(listOPs, subtype);
            for (const auto pr : listOPs) {
              const MemoryObject *existing = pr.first;
              if (existing->kind == MemKind::lazy) {

                // branch the state
                ExecutionState *existObjState = sp.second->branch();
                if (existObjState != nullptr) {

                  bool satisfyable;
                  ref<Expr> eq = EqExpr::create(e, existing->getBaseExpr());
                  if (tsolver->mayBeTrue(existObjState, eq, satisfyable) && satisfyable) {

                    // constrain the pointer
                    addConstraint(*existObjState, eq);
                    addedStates.push_back(existObjState);

                    // link new state into the process tree
                    sp.second->ptreeNode->data = nullptr;
                    std::pair<PTree::Node*, PTree::Node*> res = processTree->split(sp.second->ptreeNode, existObjState, sp.second);
                    existObjState->ptreeNode = res.first;
                    sp.second->ptreeNode = res.second;
                  } else {
                    delete existObjState;
                  }
                }
              }
            }
          }

          // finally, try with a new object
          MemoryObject *newMO = allocMemory(*sp.second, subtype, target->inst, MemKind::lazy,
                                            '*' + mo->name, 0, lazyAllocationCount);
          bindObjectInState(*sp.second, newMO);
          ref<ConstantExpr> ptr = newMO->getBaseExpr();
          ref<Expr> eq = EqExpr::create(e, ptr);
          addConstraintOrTerminate(*sp.second, eq);
        }
      }
    }
  }
  return true;
}

bool LocalExecutor::executeWriteMemoryOperation(ExecutionState &state,
                                                ref<Expr> address,
                                                ref<Expr> value,
                                                KInstruction *target,
                                                const std::string name) {

  ObjectPair op;

  ResolveResult result = resolveMO(state, address, op);
  if (result != ResolveResult::OK) {
    terminateStateOnFault(state, target, "write resolveMO");
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

  // target state may change during this call, so use indirect access
  ExecutionState *currState = &state;

  ref<Expr> offsetExpr = mo->getOffsetExpr(address);
  if (isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> coffsetExpr = cast<ConstantExpr>(offsetExpr);
    const auto offset = (unsigned) coffsetExpr->getZExtValue();
    if (offset + bytes > os->visible_size) {

      terminateStateOnFault(*currState, target, "write OoB const offset");
      return false;
    }
  } else {

    ref<Expr> mc = os->getBoundsCheckOffset(offsetExpr, bytes);

    // at most one of these forks will survive
    // currState will point to the sole survivor
    // and will be constrained inbounds
    Executor::StatePair sp = fork(*currState, mc, true);
    if (sp.first == nullptr) {
      // no satisfying inbounds solution, both currState and sp.second must terminate
      terminateStateOnFault(*currState, target, "read OoB1 offset");
      if (sp.second != nullptr && sp.second != currState) {
        terminateStateOnFault(*sp.second, target, "read OoB2 offset");
      }
      return false;

    } else {
      // inbound solution exists.  should continue as currState. sp.second must terminate
      currState = sp.first;
      if (sp.second != nullptr) {
        terminateStateOnFault(*sp.second, target, "read OoB3 offset");
      }
    }
  }
  ObjectState *wos = currState->addressSpace.getWriteable(mo, os);

  // try to convert to a constant expr
  offsetExpr = toUnique(*currState, offsetExpr);
  if (!isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> cex;
    if (tsolver->getValue(*currState, offsetExpr, cex)) {

      ref<Expr> eq = EqExpr::create(offsetExpr, cex);
      if (!addConstraintOrTerminate(*currState, eq)) {
        return false;
      }
      offsetExpr = cex;
    } else {
      terminateState(*currState);
      return false;
    }
  }
  assert(isa<ConstantExpr>(offsetExpr));
  wos->write(offsetExpr, value);
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

  unsigned size;
  if (type->isSized())  {
    if (align == 0) {
      align = kmodule->targetData->getPrefTypeAlignment(type);
    }
      size = (unsigned) (kmodule->targetData->getTypeStoreSize(type) * count);
  } else {
    if (align == 0) {
      align = 8;
    }
    size = lazyAllocationCount * count;
  }
  unsigned created_size = size;

  if ((kind == MemKind::lazy) && (size < MinLazyAllocationSize)) {
    size = MinLazyAllocationSize;
  }

  MemoryObject *mo = memory->allocate(size, type, kind, allocSite, align);
  if (mo == nullptr) {
    klee_error("Could not allocate memory for symbolic allocation");
  } else {
    mo->name = name;
    mo->count = count;
    mo->created_size = created_size;
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

  MemoryObject *mo = memory->allocate(origMO->size, origMO->created_type, origMO->kind, allocSite, origMO->align);
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

void LocalExecutor::initializeGlobalValues(ExecutionState &state, Function *fn) {

  for (auto itr = kmodule->module->global_begin(), end = kmodule->module->global_end(); itr != end; ++itr) {
    const GlobalVariable *v = static_cast<const GlobalVariable *>(itr);
    MemoryObject *mo = globalObjects.find(v)->second;
    std::string name = mo->name;
    if (state.isUnconstrainGlobals() &&
        (name.size() > 0) && (name.at(0) != '.') &&
        (fn == nullptr || progInfo->isGlobalInput(fn->getName().str(), name))) {
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

const Module *LocalExecutor::setModule(llvm::Module *module, const ModuleOptions &opts) {

  assert(kmodule == nullptr);
  const Module *result = Executor::setModule(module, opts);
  kmodule->prepareMarkers(interpreterHandler, opts.EntryPoint);
  specialFunctionHandler->setLocalExecutor(this);

  void *addr_offset = nullptr;
  if (Context::get().getPointerWidth() == Expr::Int32) {
    addr_offset = heap_base;
  }

  // prepare a generic initial state
  germinalState = new ExecutionState(addr_offset);
  germinalState->maxLoopIteration = maxLoopIteration;
  germinalState->lazyAllocationCount = lazyAllocationCount;
  germinalState->maxLazyDepth = maxLazyDepth;
  germinalState->maxLoopForks = maxLoopForks;

  initializeGlobals(*germinalState, addr_offset);
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

  for (auto it = kmodule->functions.begin(), ie = kmodule->functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    for (unsigned i = 0; i < kf->numInstructions; ++i) {
      bindInstructionConstants(kf->instructions[i]);
    }
  }
}

void LocalExecutor::runFunctionUnconstrained(Function *fn) {

  KFunction *kf = kmodule->functionMap[fn];
  if (kf == nullptr) {
    // not in this compilation unit
    return;
  }

  std::string name = fn->getName();
  kmodule->getReachablePaths(kf, m2m_pathsRemaining);
  auto num_reachable_paths = m2m_pathsRemaining.size();
  unsigned num_dropped_paths = 0;

  // iterate through each phase of unconstraint progression
  for (auto itr = progression.begin(), end = progression.end(); itr != end; ++itr) {

    const auto &desc = *itr;

    if (doLocalCoverage) {

      // done if our objective is local coverage and there are no paths remaining
      if (m2m_pathsRemaining.empty()) break;
    } else {

      // otherwise, if no prior progression phase terminated a pending state,
      // then we have covered every feasible path
      if (itr != progression.begin() && !terminatedPendingState) break;
    }

    ExecutionState *state = new ExecutionState(*germinalState, kf, name);
    timeout = desc.timeout;

    // when substituting unconstraining stubs, remaining paths
    // must be filtered to only entry function
    if (desc.unconstraintFlags.test(UNCONSTRAIN_STUB_FLAG)) {
      auto itr = m2m_pathsRemaining.begin();
      while (itr != m2m_pathsRemaining.end()) {
        const m2m_path_t &path = *itr;
        if (path.empty() || getFNID(path[0]) != kf->fnID) {
          itr = m2m_pathsRemaining.erase(itr);
          ++num_dropped_paths;
        } else {
          ++itr;
        }
      }
    }

    unconstraintFlags |= desc.unconstraintFlags;
    state->setUnconstraintFlags(unconstraintFlags);

    if (pathWriter)
      state->pathOS = pathWriter->open();
    if (symPathWriter)
      state->symPathOS = symPathWriter->open();

    if (statsTracker)
      statsTracker->framePushed(*state, nullptr);

    initializeGlobalValues(*state, fn);

    // create parameter values
    unsigned index = 0;
    for (Function::const_arg_iterator ai = fn->arg_begin(), ae = fn->arg_end(); ai != ae; ++ai, ++index) {

      const Argument &arg = *ai;
      std::string argName = arg.getName();
      Type *argType = arg.getType();
      size_t argAlign = arg.getParamAlignment();

      WObjectPair wop;
      if (!allocSymbolic(*state, argType, &arg, MemKind::param, argName, wop, argAlign)) {
        klee_error("failed to allocate function parameter");
      }
      Expr::Width width = (unsigned) kmodule->targetData->getTypeAllocSizeInBits(argType);
        ref<Expr> e = wop.second->read(0, width);
      bindArgument(kf, index, *state, e);
    }
    runFn(kf, *state);
  }
  outs() << name;
  if (doLocalCoverage) {
    outs() << ": covered "
           << num_reachable_paths - (m2m_pathsRemaining.size() + num_dropped_paths)
           << " of " << num_reachable_paths << " reachable m2m path(s)";
  }
  outs() << ": generated " << interpreterHandler->getNumTestCases() << " test case(s)\n";
  outs().flush();
}

void LocalExecutor::runFunctionAsMain(Function *f, int argc, char **argv, char **envp) {

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
    arguments.emplace_back(ConstantExpr::alloc(argc, Expr::Int32));
    if (++ai!=ae) {
      Instruction *first = static_cast<Instruction *>(f->begin()->begin());
      argvMO =
      memory->allocate((argc + 1 + envc + 1 + 1) * NumPtrBytes,
                       Type::getInt8Ty(ctx), MemKind::param, first, 8);
      
      if (!argvMO)
        klee_error("Could not allocate memory for function arguments");
      
      arguments.emplace_back(argvMO->getBaseExpr());
      
      if (++ai!=ae) {
        uint64_t envp_start = argvMO->address + (argc+1)*NumPtrBytes;
        arguments.emplace_back(Expr::createPointer(envp_start));
        
        if (++ai!=ae)
          klee_error("invalid main function (expect 0-3 arguments)");
      }
    }
  }
  
  ExecutionState *state = new ExecutionState(*germinalState, kf, name);
  
  if (pathWriter)
    state->pathOS = pathWriter->open();
  if (symPathWriter)
    state->symPathOS = symPathWriter->open();
  if (statsTracker)
    statsTracker->framePushed(*state, nullptr);

  initializeGlobalValues(*state, nullptr);

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
  
  runFn(kf, *state);
  
  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(nullptr);

  // clean up global objects
  legalFunctions.clear();
  globalObjects.clear();
  globalAddresses.clear();
  
  if (statsTracker) {
    statsTracker->done();
  }
}

void LocalExecutor::runFn(KFunction *kf, ExecutionState &initialState) {

  Function *fn = kf->function;
  if (verbose) {
    outs() << fn->getName().str() << ": " << interpreterHandler->to_string(unconstraintFlags) << '\n';
    outs().flush();
  }

  // Delay init till now so that ticks don't accrue during
  // optimization and such.
  initTimers();

  if (initialState.isUnconstrainLocals()) {
    runFnEachBlock(kf, initialState);
  } else {
    runFnFromBlock(kf, initialState, &fn->getEntryBlock());
  }
}

void LocalExecutor::runFnEachBlock(KFunction *kf, ExecutionState &initialState) {

  assert(initialState.isUnconstrainLocals());

  // create a worklist of basicblocks sorted by distance from entry
  std::deque<const llvm::BasicBlock*> worklist;
  for (auto bb : kf->sortedBBlocks) {

    // do not include blocks from the skip list in worklist
    if (skipBlocks.count(bb) == 0) {
      worklist.push_back(bb);
    }
  }

  while (!worklist.empty() && !haltExecution) {

    // of our objective is just local coverage, then we're done
    if (doLocalCoverage && m2m_pathsRemaining.empty())
      break;

    const BasicBlock *startBB = worklist.front();
    worklist.pop_front();

    if (startBB != &kf->function->getEntryBlock()) {
      if (doLocalCoverage && !reachesRemainingPath(kf, startBB)) {
        continue;
      }
      if (verbose) {
        outs() << "    starting from: ";
        if (kf->mapMarkers[startBB].empty()) {
          outs() << "unmarked block";
        } else {
          outs() << kf->mapMarkers[startBB].front();
        }
        outs() << "\n";
        outs().flush();
      }
    }
    runFnFromBlock(kf, initialState, startBB);
  }
}

LocalExecutor::HaltReason LocalExecutor::runFnFromBlock(KFunction *kf, ExecutionState &initial, const BasicBlock *start) {

  unsigned debug_value = DebugValue;

  // reset the watchdog timer
  interpreterHandler->resetWatchDogTimer();

  // set new initial program counter
  ExecutionState *initState = new ExecutionState(initial);

  unsigned entry = kf->basicBlockEntry[const_cast<BasicBlock*>(start)];
  initState->pc = &kf->instructions[entry];

  if (initState->isUnconstrainLocals()) {

    // record starting marker
    if (kf->mapMarkers[start].empty()) {
      initState->startingMarker = (unsigned) -1;
    } else {
      initState->startingMarker = kf->mapMarkers[start].front();
    }

    // unconstrain local variables
    prepareLocalSymbolics(kf, *initState);

    // if jumping into the interior of a loop, push required loop frames
    std::vector<const BasicBlock*> hdrs;
    kf->findContainingLoops(start, hdrs);

    // create loop frames in order
    StackFrame &sf = initState->stack.back();
    for (auto itr = hdrs.begin(), end = hdrs.end(); itr != end; ++itr) {
      sf.loopFrames.emplace_back(LoopFrame(*itr, getNextLoopSignature()));
    }
  }

  processTree = new PTree(initState);
  initState->ptreeNode = processTree->root;

  states.insert(initState);
  searcher = constructUserSearcher(*this);
  std::vector<ExecutionState *> newStates(states.begin(), states.end());
  searcher->update(nullptr, newStates, std::vector<ExecutionState *>());

  struct timespec tm;
  clock_gettime(CLOCK_MONOTONIC, &tm);
  uint64_t now = (uint64_t) tm.tv_sec;
  uint64_t stopTime = timeout == 0 ? UINT64_MAX : now + timeout;
  uint64_t heartbeat = now + HEARTBEAT_INTERVAL;
  HaltReason halt = HaltReason::OK;

  while (!states.empty()) {

    if (haltExecution || halt != HaltReason::OK) break;
    if (doLocalCoverage && m2m_pathsRemaining.empty()) break;
    ExecutionState *state;

    state = &searcher->selectState();
    KInstruction *ki = state->pc;
    stepInstruction(*state);
    try {

      // RLR TODO: convenience statement for debugging
      if (ki->info->assemblyLine == debug_value) {
        debug_break();
      }

      executeInstruction(*state, ki);
    } catch (bad_expression &e) {
      halt = HaltReason::InvalidExpr;
      outs() << "    * uninitialized expression, halting execution\n";
    }

    processTimers(state, 0);
    updateStates(state);

    // check for exceeding maximum time
    clock_gettime(CLOCK_MONOTONIC, &tm);
    now = (uint64_t) tm.tv_sec;
    if (now > stopTime) {
      outs() << "    * max time elapsed, halting execution\n";
      halt = HaltReason::TimeOut;
    } else if (now > heartbeat) {
      interpreterHandler->resetWatchDogTimer();
      heartbeat = now + HEARTBEAT_INTERVAL;
    }
    checkMemoryFnUsage(kf);
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

  if (state.status == ExecutionState::StateStatus::Pending) {
    terminatedPendingState = true;
  }

  if (doSaveComplete && state.status == ExecutionState::StateStatus::Completed) {
    if (removeCoveredPaths(&state)) {
      interpreterHandler->processTestCase(state);
    }
  } else if (doSaveFault && state.status == ExecutionState::StateStatus::Faulted) {
    interpreterHandler->processTestCase(state);
  }
  Executor::terminateState(state);
}

void LocalExecutor::terminateStateOnExit(ExecutionState &state) {
  state.status = ExecutionState::StateStatus::Completed;
  Executor::terminateStateOnExit(state);
}

void LocalExecutor::terminateStateOnFault(ExecutionState &state, const KInstruction *ki, const llvm::Twine &message) {
  state.status = ExecutionState::StateStatus::Faulted;
  state.instFaulting = ki;
  state.terminationMessage = message.str();
  Executor::terminateStateOnExit(state);
}

void LocalExecutor::terminateStateEarly(ExecutionState &state, const llvm::Twine &message) {
  state.status = ExecutionState::StateStatus::TerminateEarly;
  Executor::terminateStateEarly(state, message);
}

void LocalExecutor::terminateStateOnError(ExecutionState &state, const llvm::Twine &message,
                           enum TerminateReason termReason,
                           const char *suffix,
                           const llvm::Twine &longMessage) {
  state.status = ExecutionState::StateStatus::TerminateError;
  Executor::terminateStateOnError(state, message, termReason, suffix, longMessage);
}

void LocalExecutor::checkMemoryFnUsage(KFunction *kf) {

  Executor::checkMemoryUsage();

  if ((stats::instructions & 0xFFF) == 0) {
    if (kf != nullptr) {
      for (const auto pair : kf->loopInfo) {
        const BasicBlock *hdr = pair.first;
        unsigned num = numStatesInLoop(hdr);
        if (num > maxStatesInLoop) {
          unsigned killed = decimateStatesInLoop(hdr, 99);
          outs() << "terminated " << killed << " states in loop: " << kf->mapMarkers[hdr].front() << "\n";
        }
      }
    }
  }
}

unsigned LocalExecutor::decimateStatesInLoop(const BasicBlock *hdr, unsigned skip_counter) {

  unsigned counter = 0;
  unsigned killed = 0;
  skip_counter++;
  for (ExecutionState *state : states) {
    if (!state->stack.empty()) {
      const StackFrame &sf = state->stack.back();
      if (!sf.loopFrames.empty()) {
        const LoopFrame &lf = sf.loopFrames.back();
        if ((lf.hdr == hdr) && (++counter % skip_counter != 0)) {
          terminateState(*state);
          killed++;
        }
      }
    }
  }
  return killed;
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

bool LocalExecutor::removeCoveredPaths(const ExecutionState *state) {

  bool result = false;
  std::map<unsigned,m2m_path_t> traces;
  state->markers.to_intra_traces(traces);
  auto itr = m2m_pathsRemaining.begin();
  auto end = m2m_pathsRemaining.end();
  while (itr != end) {

    const m2m_path_t &path = *itr;
    unsigned fnID = getFNID(path[0]);
    m2m_path_t &intra_trace = traces[fnID];

    auto found = std::search(intra_trace.begin(), intra_trace.end(), path.begin(), path.end());
    if (found == intra_trace.end()) {
      ++itr;
    } else {
      itr = m2m_pathsRemaining.erase(itr);
      result = true;
    }
  }
  return result;
}

bool LocalExecutor::reachesRemainingPath(KFunction *kf, const llvm::BasicBlock *bb) const {

  // construct a set of m2m path headers
  std::set<const BasicBlock*> path_headers;
  for (auto path : m2m_pathsRemaining) {
    assert(!path.empty());
    unsigned head = getMKID(path.front());
    auto itr = kf->mapBBlocks.find(head);
    if (itr != kf->mapBBlocks.end() && itr->second != nullptr) {
      path_headers.insert(itr->second);
    }
  }

  if (path_headers.empty()) {
    return false;
  }
  return kf->reachesAnyOf(bb, path_headers);
}

ref<ConstantExpr> LocalExecutor::ensureUnique(ExecutionState &state, const ref<Expr> &e) {

  ref<ConstantExpr> result;

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e)) {
    result = CE;
  } else {
    if (tsolver->getValue(state, e, result)) {

      bool answer = false;
      ref<Expr> eq = EqExpr::create(e, result);
      if (tsolver->mustBeTrue(state, eq, answer) && !answer) {
        addConstraint(state, eq);
      }
    }
  }
  return result;
}

bool LocalExecutor::isUnique(const ExecutionState &state, ref<Expr> &e) const {

  bool result = false;
  if (isa<ConstantExpr>(e)) {
    result = true;
  } else {

    ref<ConstantExpr> value;
    if (tsolver->getValue(state, e, value)) {

      bool answer = false;
      ref<Expr> eq = EqExpr::create(e, value);
      if (tsolver->mustBeTrue(state, eq, answer)) {
        result = answer;
      }
    }
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
        sf.loopFrames.emplace_back(LoopFrame(dst, getNextLoopSignature()));
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

void LocalExecutor::prepareLocalSymbolics(KFunction *kf, ExecutionState &state) {

  assert(state.isUnconstrainLocals());

  // iterate over the entry block and execute allocas
  Function *fn = kf->function;
  if (fn->size() > 0) {

    // loop through twice, the first time we only perform allocations
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

        bool to_symbolic = !ki->inst->getName().empty();
        executeAlloc(state, size, 1, ai->getAllocatedType(), MemKind::alloca, ki, to_symbolic);
      }
    }

    // the second time, we perform initializations
    pc = kf->instructions;
    cur = nullptr;
    unsigned numArgs = (unsigned) fn->arg_size();
    while (cur != end && numArgs > 0) {
      KInstruction *ki = pc;
      ++pc;
      cur = ki->inst;

      if (const AllocaInst *ai = dyn_cast<AllocaInst>(cur)) {

        (void) ai;
        // skip over it

      } else if (const BitCastInst *bc = dyn_cast<BitCastInst>(cur)) {

        (void) bc;
        ref<Expr> result = eval(ki, 0, state).value;
        bindLocal(ki, state, result);

      } else if (const StoreInst *si = dyn_cast<StoreInst>(cur)) {

        // the first numArg store operations setup the arguments
        if (numArgs > 0) {
          const Value *v = si->getValueOperand();
          if (v->hasName()) {
            std::string name = v->getName().str();
            ref<Expr> base = eval(ki, 1, state).value;
            ref<Expr> value = eval(ki, 0, state).value;
            executeWriteMemoryOperation(state, base, value, ki, name);
            // after the last store, no need to scan further into entry block
            --numArgs;
          }
        }
      } else if (const GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(cur)) {

        (void) gep;
        KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
        ref<Expr> base = eval(ki, 0, state).value;
        ref<Expr> offset = ConstantExpr::ConstantExpr::create(0, base->getWidth());

        ObjectPair op;
        ResolveResult result = resolveMO(state, base, op);
        if (result == ResolveResult::OK) {
          for (auto it = kgepi->indices.begin(), ie = kgepi->indices.end(); it != ie; ++it) {
            uint64_t elementSize = it->second;
            ref<Expr> index = eval(ki, it->first, state).value;

            offset = AddExpr::create(offset,
                                     MulExpr::create(Expr::createSExtToPointerWidth(index),
                                                     Expr::createPointer(elementSize)));
          }
          if (kgepi->offset) {
            offset = AddExpr::create(offset, Expr::createPointer(kgepi->offset));
          }
          base = AddExpr::create(base, offset);
          bindLocal(ki, state, base);
        } else {
          klee_warning("Unable to resolve gep base during preparation of local symbolics");
        }
      } else {
        klee_warning("Unexpected instruction during preparation of local symbolics");
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
        assert(bi->getCondition() == bi->getOperand(0) && "Wrong operand index!");
        state.allBranchCounter++;
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
              states[index]->unconBranchCounter++;
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
      std::string fnName = "unknown";
      Function *fn = getTargetFunction(cs.getCalledValue(), state);
      if (fn != nullptr) {
        fnName = fn->getName();

        // if this function does not return, (exit, abort, zopc_exit, etc)
        // then this state has completed
        if (fn->hasFnAttribute(Attribute::NoReturn)) {

          if (fnName == "zopc_exit" || fnName == "exit") {
            terminateStateOnExit(state);
          } else if (fnName == "abort") {

          // RLR TODO: is an abort an fault?
            terminateStateOnExit(state);
          } else if (fnName == "__assert_fail") {
            terminateStateOnError(state, "assertion failed", TerminateReason::Assert);
          } else {
            terminateStateOnError(state, "unknown exit", TerminateReason::Unhandled);
          }
          return;
        }

        // if this is a call to a mark() variant, then log the marker to state
        // ':' is an invalid marker type
        char marker_type = ':';
        if (fnName == "MARK") {
          marker_type = 'M';
        } else if (fnName == "mark") {
          marker_type = 'm';
        } else if (fnName == "fn_tag") {
          marker_type = 't';
        }

        if ((marker_type != ':') && (fn->arg_size() == 2) && (fn->getReturnType()->isVoidTy())) {

          const Constant *arg0 = dyn_cast<Constant>(cs.getArgument(0));
          const Constant *arg1 = dyn_cast<Constant>(cs.getArgument(1));
          if ((arg0 != nullptr) && (arg1 != nullptr)) {
            unsigned fnID = (unsigned) arg0->getUniqueInteger().getZExtValue();
            unsigned bbID = (unsigned) arg1->getUniqueInteger().getZExtValue();

            state.addMarker(marker_type, fnID, bbID);
            return;
          }
        }
      } else {
        fnName = "still_unknown";

        // RLR TODO: lookup something appropriate
        // should also check to see if this is a unique ptr.
        // do something meaningfull if so.  check for null ptr.
      }

      // if subfunctions are not stubbed, this is a special function, or
      // this is an internal klee fuction, then let the standard executor handle it
      bool isInModule = false;
      if (fn != nullptr) {
        isInModule = kmodule->isModuleFunction(fn);
        if ((!state.isStubCallees() && isInModule) ||
            specialFunctionHandler->isSpecial(fn) ||
            kmodule->isInternalFunction(fn)) {
          Executor::executeInstruction(state, ki);
          return;
        }
      }

      // we will be simulating a stubbed subfunction.

      // hence, this is a function in this module
      unsigned counter = state.callTargetCounter[fnName]++;

      // consider the arguments pushed for the call, rather than
      // args expected by the target
      unsigned numArgs = cs.arg_size();
      if (fn == nullptr || !fn->isVarArg()) {
        for (unsigned index = 0; index < numArgs; ++index) {
          const Value *v = cs.getArgument(index);
          Type *argType = v->getType();

          if ((countLoadIndirection(argType) > 0) && !progInfo->isConstParam(fnName, index)) {

            ref<Expr> exp_addr = eval(ki, index + 1, state).value;
            ObjectPair op;

            // find the referenced memory object
            if (resolveMO(state, exp_addr, op) == ResolveResult::OK) {
              const MemoryObject *orgMO = op.first;
              const ObjectState *orgOS = op.second;

              ref<Expr> e = orgOS->getBoundsCheckPointer(exp_addr);
              bool result = false;
              if (tsolver->mayBeTrue(state, e, result) && result) {
                addConstraint(state, e);

                ref<ConstantExpr> address = ensureUnique(state, exp_addr);
                ObjectState *argOS = state.addressSpace.getWriteable(orgMO, orgOS);
                Type *eleType = argType->getPointerElementType();
                unsigned eleSize;
                if (eleType->isSized()) {
                  eleSize = (unsigned) kmodule->targetData->getTypeAllocSize(eleType);
                } else {
                  eleSize = lazyAllocationCount;
                }
                unsigned offset = (unsigned) (address->getZExtValue() - orgMO->address);
                unsigned count = (orgOS->visible_size - offset) / eleSize;

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
              }
            }
          }
        }
      }

      // unconstrain global variables
      if (isInModule && state.isUnconstrainGlobals()) {
        unconstrainGlobals(state, fn, counter);
      }

      // now get the return type
      Type *ty = cs->getType();
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
          ref<Expr> eqNull = EqExpr::create(retExpr, null);
          StatePair sp = fork(state, eqNull, true);

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
                  bool success = tsolver->mayBeTrue(state, UltExpr::create(size, min_size), result);
                  assert(success && "FIXME: Unhandled solver failure");
                }
                if (result) {
                  addConstraint(*sp.second, UltExpr::create(size, min_size));
                  bool success = tsolver->getValue(*sp.second, size, min_size);
                  assert(success && "FIXME: solver just said mayBeTrue");
                  ref<Expr> eq = EqExpr::create(size, min_size);
                  addConstraint(*sp.second, eq);
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
            ref<Expr> eq = EqExpr::create(retExpr, ptr);
            addConstraint(*sp.second, eq);
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
      ref<Expr> offset = ConstantExpr::ConstantExpr::create(0, base->getWidth());

      ObjectPair op;
      ResolveResult result = resolveMO(state, base, op);
      if (result == ResolveResult::OK) {
        const MemoryObject *mo = op.first;
        const ObjectState *os = op.second;

        assert(i->getType()->isPtrOrPtrVectorTy());

        for (auto it = kgepi->indices.begin(), ie = kgepi->indices.end(); it != ie; ++it) {
          uint64_t elementSize = it->second;
          ref<Expr> index = eval(ki, it->first, state).value;

          offset = AddExpr::create(offset,
                                   MulExpr::create(Expr::createSExtToPointerWidth(index),
                                                 Expr::createPointer(elementSize)));
        }
        if (kgepi->offset) {
          offset = AddExpr::create(offset, Expr::createPointer(kgepi->offset));
        }

        // if we are looking for faults and
        // this is a base pointer into a lazy init with a non-zero offset,
        // then this could be a memory bounds fail.
        if (doSaveFault && mo->kind == MemKind::lazy) {
          bool ans = false;
          if (tsolver->mayBeTrue(state, Expr::createIsZero(offset), ans) && ans) {

            // generate a test case
            const KInstruction *prior = state.instFaulting;
            state.instFaulting = ki;
            interpreterHandler->processTestCase(state);
            state.instFaulting = prior;
          }
        }

        base = AddExpr::create(base, offset);

        // if we are in zop mode, insure the pointer is inbounds
        if (doAssumeInBounds) {

          Expr::Width width = getWidthForLLVMType(i->getType()->getPointerElementType());
          unsigned bytes = Expr::getMinBytesForWidth(width);

          // base must point into an allocation
          bool answer;
          ref<Expr> mc = os->getBoundsCheckPointer(base, bytes);

          if (tsolver->mustBeTrue(state, mc, answer) && !answer) {
            if (tsolver->mayBeTrue(state, mc, answer) && answer) {
              addConstraint(state, mc);
            }
          }
        }

        bindLocal(ki, state, base);
      } else {

        // invalid memory access, fault at ki and base
        terminateStateOnFault(state, ki, "GEP resolveMO");
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
      executeWriteMemoryOperation(state, base, value, ki, name);
      break;
    }

    case Instruction::BitCast: {
      CastInst *ci = cast<CastInst>(i);
      Type *srcTy = ci->getSrcTy();
      Type *destTy = ci->getDestTy();

      if (srcTy->isPointerTy() && destTy->isPointerTy()) {
        Type *srcPtd = srcTy->getPointerElementType();
        Type *destPtd = destTy->getPointerElementType();
        unsigned srcSize = kmodule->targetData->getLargestLegalIntTypeSize();
        unsigned destSize = srcSize;
        if (srcPtd->isSized()) {
          srcSize = (unsigned) kmodule->targetData->getTypeStoreSize(srcPtd);
        }
        if (destPtd->isSized()) {
          destSize = (unsigned) kmodule->targetData->getTypeStoreSize(destPtd);
        }

        if ((srcTy != destTy) || (srcSize < destSize)) {
          ref<Expr> ptr = eval(ki, 0, state).value;

          ObjectPair op;
          if (resolveMO(state, ptr, op) == ResolveResult::OK) {

            const MemoryObject *mo = op.first;
            const ObjectState *os = op.second;
            if (mo->kind == MemKind::lazy) {

              if (destSize > mo->size) {
                // not even one will fit
                klee_warning("lazy init size too small for bitcast");
              }

              destSize *= lazyAllocationCount;
              destSize = std::min(destSize, mo->size);
              if (destSize > os->visible_size) {
                ObjectState *wos = state.addressSpace.getWriteable(mo, os);
                wos->visible_size = destSize;
              }

              // pointed type change
              if (srcPtd != destPtd) {

                // only record if this is a pointer to the beginning of a memory object
                ref<Expr> is_zero = Expr::createIsZero(mo->getOffsetExpr(ptr));

                bool result = false;
                if (tsolver->mayBeTrue(state, is_zero, result) && result) {
                  ObjectState *wos = state.addressSpace.getWriteable(mo, os);
                  wos->types.push_back(destTy);
                }
              }
            }
          }
        }
      }

      ref<Expr> result = eval(ki, 0, state).value;
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::FCmp:
      Executor::executeInstruction(state, ki);
      klee_warning("Floating point comparison");
      break;

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
      const MemoryObject *mo = sym.first;
      const ObjectState *os = state->addressSpace.findObject(mo);

      assert(os->getLastType() != nullptr);

      std::string name = mo->name;
      const llvm::Type *type = os->getLastType();
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
                                      InterpreterHandler *ih) {
  return new LocalExecutor(ctx, opts, ih);
}

}

///

