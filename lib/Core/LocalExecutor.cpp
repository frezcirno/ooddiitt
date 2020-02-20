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
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/MemoryUsage.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Support/CallSite.h"

#include <boost/algorithm/string.hpp>
#include <llvm/IR/Intrinsics.h>

#define LEN_CMDLINE_ARGS 8

using namespace llvm;
using namespace std;

namespace klee {

class bad_expression : public std::runtime_error
{
public:
  bad_expression() : std::runtime_error("null expression") {}
  bad_expression(const char *msg) : std::runtime_error(msg) {}
};


class Tracer {
  virtual unsigned to_entry(KInstruction *ki);
};

cl::opt<unsigned> SymArgs("sym-args", cl::init(4), cl::desc("Maximum number of command line arguments (only used when entry-point is main)"));
cl::opt<bool> SavePendingStates("save-pending-states", cl::init(false), cl::desc("at timeout, save states that have not completed"));
cl::opt<bool> SaveFaultingStates("save-faulting-states", cl::init(false), cl::desc("save states that have faulted"));
cl::opt<unsigned> LazyAllocationCount("lazy-allocation-count", cl::init(4), cl::desc("Number of items to lazy initialize pointer"));
cl::opt<unsigned> LazyStringLength("lazy-string-length", cl::init(9), cl::desc("Number of characters to lazy initialize i8 ptr"));
cl::opt<unsigned> LazyAllocationOffset("lazy-allocation-offset", cl::init(0), cl::desc("index into lazy allocation to return"));
cl::opt<unsigned> MinLazyAllocationSize("lazy-allocation-minsize", cl::init(0), cl::desc("minimum size of a lazy allocation"));
cl::opt<unsigned> LazyAllocationDepth("lazy-allocation-depth", cl::init(4), cl::desc("Depth of items to lazy initialize pointer"));
cl::opt<unsigned> LazyAllocationExt("lazy-allocation-ext", cl::init(0), cl::desc("number of lazy allocations to include existing memory objects of same type"));
cl::opt<unsigned> MaxLoopIteration("max-loop-iteration", cl::init(4), cl::desc("Number of loop iterations"));
cl::opt<unsigned> MaxLoopForks("max-loop-forks", cl::init(16), cl::desc("Number of forks within loop body"));
cl::opt<unsigned> MaxLoopStates("max-loop-states", cl::init(0), cl::desc("Number of states within loop body"));
cl::opt<string> BreakAt("break-at", cl::desc("break at the given trace line number or function name"));

LocalExecutor::LocalExecutor(LLVMContext &ctx, const InterpreterOptions &opts, InterpreterHandler *ih) :
  Executor(ctx, opts, ih),
  lazyAllocationCount(LazyAllocationCount),
  lazyStringLength(LazyStringLength),
  maxLoopIteration(MaxLoopIteration),
  maxLoopForks(MaxLoopForks),
  maxLazyDepth(LazyAllocationDepth),
  maxStatesInLoop(MaxLoopStates),
  baseState(nullptr),
  timeout(0),
  progression(opts.progression),
  libc_initializing(false),
  enable_state_switching(true),
  sysModel(nullptr),
  trace_type(TraceType::invalid),
  moStdInBuff(nullptr),
  tracer(nullptr) {

  switch (opts.mode) {
    case ExecModeID::prep:
      doSaveFault = false;
      doAssumeInBounds = false;
      doLocalCoverage = false;
      doConcreteInterpretation = false;
      doModelStdOutput = true;
      break;
    case ExecModeID::igen:
      doSaveFault = false;
      doAssumeInBounds = true;
      doLocalCoverage = false;
      doConcreteInterpretation = false;
      doModelStdOutput = true;
      break;
    case ExecModeID::rply:
      doSaveFault = false;
      doAssumeInBounds = false;
      doLocalCoverage = false;
      doConcreteInterpretation = true;
      doModelStdOutput = false;
      break;
    case ExecModeID::irec:
      doSaveFault = false;
      doAssumeInBounds = false;
      doLocalCoverage = false;
      doConcreteInterpretation = true;
      doModelStdOutput = true;
      break;
    default:
      klee_error("invalid execution mode");
  }
  optsModel.doModelStdOutput = doModelStdOutput;
}

LocalExecutor::~LocalExecutor() {

  if (sysModel != nullptr) {
    delete sysModel;
    sysModel = nullptr;
  }

  if (statsTracker) {
    statsTracker->done();
  }

  if (baseState != nullptr) {
    // RLR TODO: evaluate solver teardown
    // this last state is leaked.  something in solver
    // tear-down does not like its deletion
    delete baseState;
    baseState = nullptr;
  }
}

bool LocalExecutor::addConstraintOrTerminate(ExecutionState &state, ref<Expr> e) {

  if (solver->mayBeTrue(state, e)) {
    addConstraint(state, e);
    return true;
  }

  // WARNING: if this function returns false, state must not be accessed again
  terminateState(state, "added invalid constraint");
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
  bool result = false;
  if (!state.addressSpace.resolveOne(state, solver, address, true, op, result)) {

    ref<ConstantExpr> caddr;
    if (solver->getValue(state, address, caddr)) {
      return resolveMO(state, caddr, op);
    }
  }
  return result ? ResolveResult::OK : ResolveResult::NoObject;
}

void LocalExecutor::executeSymbolicAlloc(ExecutionState &state,
                                         unsigned size,
                                         unsigned count,
                                         const llvm::Type *type,
                                         MemKind kind,
                                         KInstruction *target,
                                         bool symbolic) {

  size_t allocationAlignment = getAllocationAlignment(target->inst);
  MemoryObject *mo = memory->allocate(size, type, kind, target->inst, allocationAlignment);
  if (!mo) {
    bindLocal(target, state, ConstantExpr::alloc(0, Context::get().getPointerWidth()));
  } else {

    string name;
    const Instruction *inst = target->inst;
    if (target->inst != nullptr && target->inst->hasName()) {
      name = inst->getName();
      if (const BasicBlock *bb = inst->getParent()) {
        const Function *fn = bb->getParent();
        if (fn != nullptr && fn->hasName()) {
          name = fn->getName().str() + '.' + name;
        }
      }
    }
    mo->name = name;
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
      }
    } else {

      // when executing at the function/fragment level, memory objects
      // may not exist. this is not an error.
    }
    if (target) {
      bindLocal(target, *zeroPointer.second, Expr::createPointer(0));
    }
  }
}

bool LocalExecutor::isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e) const {

  if (!isa<ConstantExpr>(e)) {

    Expr::Width width = Context::get().getPointerWidth();
    if (e->getWidth() == width) {

      e = state.constraints.simplifyExpr(e);

      // ensure this is a simple expression, i.e. only concats of constant reads in the tree of subexprs
      bool simple = true;

      // RLR TODO: detect unconstrained pointer
#if 0 == 1
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
#endif

      if (simple) {
        ref<ConstantExpr> max = Expr::createPointer(width == Expr::Int32 ? UINT32_MAX : UINT64_MAX);
        ref<Expr> eqMax = EqExpr::create(e, max);

        return solver->mayBeTrue(state, eqMax);
      }
    }
  }
  return false;
}

bool LocalExecutor::isReadExpr(ref<Expr> e) const {

  Expr::Kind k = e->getKind();
  if (k == Expr::Kind::Read) {
    return true;
  } else if (k == Expr::Kind::Concat) {
    ref<ConcatExpr> ce = dyn_cast<ConcatExpr>(e);
    return (ce->getLeft()->getKind() == Expr::Kind::Read) && (isReadExpr(ce->getRight()));
  } else {
    return false;
  }
}

void LocalExecutor::newUnconstrainedGlobalValues(ExecutionState &state, Function *fn, unsigned counter) {

  Module *m = kmodule->module;
  for (Module::const_global_iterator itr = m->global_begin(), end = m->global_end(); itr != end; ++itr) {
    const GlobalVariable *v = static_cast<const GlobalVariable *>(itr);
    MemoryObject *mo = globalObjects.find(v)->second;

    std::string varName = mo->name;
    if ((!varName.empty()) && (varName.at(0) != '.') /* && progInfo->isGlobalInput(state.name, varName) */) {

      std::string fnName = "unknown";
      bool unconstrain = false;
      if (fn != nullptr) {
        fnName = fn->getName().str();
        unconstrain = /* progInfo->isReachableOutput(fnName, varName) */ true;
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

bool LocalExecutor::executeReadMemoryOperation(ExecutionState &state, ref<Expr> address, const Type *type, KInstruction *target) {

  ObjectPair op;
  ResolveResult result = resolveMO(state, address, op);
  if (result != ResolveResult::OK) {

#if 0 == 1
    // RLR TODO: here be debug statements
    map<uint64_t,const MemoryObject*> addresses;
    for (auto obj : state.addressSpace.objects) {
      uint64_t addr = obj.first->address;
      addresses.insert(make_pair(obj.first->address, obj.first));
    }
    size_t size = addresses.size();
    for (auto pr : addresses) {
      uint64_t addr = pr.first;
      const MemoryObject *mo = pr.second;
      errs() << addr << ':' << mo << '\n';
    }
#endif

    terminateStateOnMemFault(state, target, "read resolveMO");
    return false;
  }

  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  Expr::Width width = getWidthForLLVMType(target->inst->getType());
  unsigned bytes = Expr::getMinBytesForWidth(width);

  // target state may change during this call, so use indirect access
  ExecutionState *currState = &state;

  ref<Expr> offsetExpr = mo->getOffsetExpr(address);
  offsetExpr = toUnique(state, offsetExpr);
  if (isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> coffsetExpr = cast<ConstantExpr>(offsetExpr);
    const auto offset = (unsigned) coffsetExpr->getZExtValue();
    if (offset + bytes - 1 > os->visible_size) {
      terminateStateOnMemFault(*currState, target, "read OoB const offset");
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
      terminateStateOnMemFault(*currState, target, "read OoB1 offset");
      if (sp.second != nullptr && sp.second != currState) {
        terminateStateOnMemFault(*sp.second, target, "read OoB2 offset");
      }
      return false;

    } else {
      // inbound solution exists.  should continue as currState. sp.second must terminate
      currState = sp.first;
      if (sp.second != nullptr) {
        terminateStateOnMemFault(*sp.second, target, "read OoB3 offset");
      }
    }
  }

  if (!doConcreteInterpretation) {
    if (!currState->isSymbolic(mo)) {
      if (!isLocallyAllocated(*currState, mo)) {
        if (mo->isLazy()) {
          outs() << "RLR: Does this ever actually happen?\n";
          os = makeSymbolic(*currState, mo);
        }
      }
    }
  }

  ref<Expr> e = os->read(offsetExpr, width);
  bindLocal(target, *currState, e);

  if (!doConcreteInterpretation && (countLoadIndirection(type) > 1) && isUnconstrainedPtr(*currState, e)) {

    // give a meaningful name to the symbolic variable.
    // do not have original c field names, so use field index
    string name = mo->name;
    string suffix;
    if (const StructType *st = dyn_cast<StructType>(mo->type)) {
      if (isa<ConstantExpr>(offsetExpr)) {
        unsigned offset = cast<ConstantExpr>(offsetExpr)->getZExtValue();
        const StructLayout *targetStruct = kmodule->targetData->getStructLayout(const_cast<StructType*>(st));
        unsigned index = targetStruct->getElementContainingOffset(offset);
        suffix= std::to_string(index);
      } else {
        suffix = "?";
      }
    }
    if (!suffix.empty()) name += ':' + suffix;

    // this is an unconstrained ptr-ptr.
    expandLazyAllocation(state, e, type->getPointerElementType(), target, name);
  }
  return true;
}

void LocalExecutor::expandLazyAllocation(ExecutionState &state,
                                         ref<Expr> addr,
                                         const llvm::Type *type,
                                         KInstruction *target,
                                         const std::string &name,
                                         bool allow_null) {

  assert(type->isPointerTy());

  Type *base_type = type->getPointerElementType();
  if (base_type->isFirstClassType()) {

    // count current depth of lazy allocations
    unsigned depth = 0;
    for (auto end = (unsigned) name.size(); depth < end && name.at(depth) == '*'; ++depth);

    ref<ConstantExpr> null = Expr::createPointer(0);
    ref<Expr> eqNull = EqExpr::create(addr, null);

    if (depth >= maxLazyDepth) {

      if (allow_null) {
        // too deep. no more forking for this pointer.
        addConstraintOrTerminate(state, eqNull);
      } else {
        terminateState(state, "memory depth exceeded");
      }
      // must not touch state again in case of failure

    } else {

      ExecutionState *next_fork;
      if (allow_null) {
        StatePair sp = fork(state, eqNull, true);

        // in the true case, ptr is null, so nothing further to do
        next_fork = sp.second;
      } else {
        next_fork = &state;
      }

      // in the false case, allocate new memory for the ptr and
      // constrain the ptr to point to it.
      if (next_fork != nullptr) {

        // pointer may not be null
        if (LazyAllocationExt > 0) {

          unsigned counter = 0;

          // consider any existing objects in memory of the same type
          std::vector<ObjectPair> listOPs;
          next_fork->addressSpace.getMemoryObjects(listOPs, base_type);
          for (const auto &pr : listOPs) {

            if (next_fork == nullptr || counter >= LazyAllocationExt)
              break;

            const MemoryObject *existingMO = pr.first;
            if (existingMO->isLazy()) {

              // fork a new state
              ref<ConstantExpr> ptr = existingMO->getBaseExpr();
              ref<Expr> eq = EqExpr::create(addr, ptr);
              StatePair sp = fork(*next_fork, eq, true);
              counter += 1;
              next_fork = sp.second;
            }
          }
        }
        if (next_fork != nullptr) {

          // calc lazyAllocationCount by type i8* (string, byte buffer) gets more
          unsigned count = LazyAllocationCount;
          if (base_type->isIntegerTy(8) && count < lazyStringLength) {
            count = lazyStringLength;
          }

          // finally, try with a new object
          WObjectPair wop;
          if (allocSymbolic(*next_fork, base_type, target->inst, MemKind::lazy, '*' + name, wop, 0, count)) {
            ref<ConstantExpr> ptr = wop.first->getOffsetIntoExpr(LazyAllocationOffset * (wop.first->created_size / count));
            ref<Expr> eq = EqExpr::create(addr, ptr);
            if (addConstraintOrTerminate(*next_fork, eq)) {
              // insure strings are null-terminated
              if (base_type->isIntegerTy(8)) {
                addConstraint(*next_fork, EqExpr::create(wop.second->read8(count - 1), ConstantExpr::create(0, Expr::Int8)));
              }
            } else {
              // state was terminated
            }
          } else {
            terminateState(*next_fork, "lazy symbolic allocation failed");
          }
        }
      }
    }
  } else if (base_type->isFunctionTy()) {
    // just say NO to function pointers
    ref<Expr> eqNull = EqExpr::create(addr, Expr::createPointer(0));
    addConstraintOrTerminate(state, eqNull);
    // do not touch state again, in case of termination
  } else {
    ostringstream ss;
    ss << "lazy initialization of unknown type: " << to_string(base_type);
    log_warning(ss, state, target);
  }
}

bool LocalExecutor::executeWriteMemoryOperation(ExecutionState &state,
                                                ref<Expr> address,
                                                ref<Expr> value,
                                                KInstruction *target,
                                                const std::string &name) {

  ObjectPair op;

  ResolveResult result = resolveMO(state, address, op);
  if (result != ResolveResult::OK) {

#if 0 == 1
    // RLR TODO: here be debug statements
    map<uint64_t,const MemoryObject*> addresses;
    for (auto obj : state.addressSpace.objects) {
      uint64_t addr = obj.first->address;
      addresses.insert(make_pair(obj.first->address, obj.first));
    }
    size_t size = addresses.size();
    for (auto pr : addresses) {
      uint64_t addr = pr.first;
      const MemoryObject *mo = pr.second;
      errs() << addr << ':' << mo << '\n';
    }
#endif

    terminateStateOnMemFault(state, target, "write resolveMO");
    return false;
  }

  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  if (os->readOnly) {
    terminateStateOnError(state, TerminateReason::ReadOnly, "memory error: object read only");
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

      terminateStateOnMemFault(*currState, target, "write OoB const offset");
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
      terminateStateOnMemFault(*currState, target, "read OoB1 offset");
      if (sp.second != nullptr && sp.second != currState) {
        terminateStateOnMemFault(*sp.second, target, "read OoB2 offset");
      }
      return false;

    } else {
      // inbound solution exists.  should continue as currState. sp.second must terminate
      currState = sp.first;
      if (sp.second != nullptr) {
        terminateStateOnMemFault(*sp.second, target, "read OoB3 offset");
      }
    }
  }
  ObjectState *wos = currState->addressSpace.getWriteable(mo, os);

  // try to convert to a constant expr
  offsetExpr = toUnique(*currState, offsetExpr);
  if (!isa<ConstantExpr>(offsetExpr)) {
    ref<ConstantExpr> cex;
    if (solver->getValue(*currState, offsetExpr, cex)) {
      ref<Expr> eq = EqExpr::create(offsetExpr, cex);
      if (!solver->mustBeTrue(*currState, eq)) {
        log_warning("Concretized offset on write", state, target);
        if (!addConstraintOrTerminate(*currState, eq)) {
          return false;
        }
      }
      offsetExpr = cex;
    } else {
      terminateStateOnMemFault(*currState, target, "write memory solver unable to get example offset");
      return false;
    }
  }
  assert(isa<ConstantExpr>(offsetExpr));
  wos->write(offsetExpr, value);
  return true;
}

ObjectState *LocalExecutor::makeSymbolic(ExecutionState &state, const MemoryObject *mo) {

  assert(!doConcreteInterpretation);

  ObjectState *wos = nullptr;
  const ObjectState *os = state.addressSpace.findObject(mo);
  if (os != nullptr) {
    wos = state.addressSpace.getWriteable(mo, os);
    if (state.isSymbolic(mo)) {
      return wos;
    }
  }

  if (mo->created_size > 4096) {
    ostringstream ss;
    ss << "large symbolic: " << mo->name << " (size=" << mo->created_size << ")";
    log_warning(ss, state);
  }

  // wos with either equal os or point to a copied value
  // os now may be been deleted, so henceforth, use wos
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
  mo->name = uniqueName;
  const Array *array = arrayCache.CreateArray(uniqueName, mo->size);

  // hold the old object state in memory
  wos = bindObjectInState(state, mo, array);
  state.addSymbolic(mo, array);
  if (!oh.isNull()) {
    wos->cloneWritten(oh.getOS());
  }
  return wos;
}

MemoryObject *LocalExecutor::allocMemory(ExecutionState &state,
                                         Type *type,
                                         const Value *allocSite,
                                         MemKind kind,
                                         const string &name,
                                         size_t align,
                                         unsigned count) {

  unsigned size;
  if (type->isSized())  {
    if (align == 0) {
      align = kmodule->targetData->getPrefTypeAlignment(type);
    }
      size = (unsigned) (kmodule->targetData->getTypeStoreSize(type) * count);
  } else {

    size = (Context::get().getPointerWidth()/8) * count;
    if (align == 0) {
      align = 8;
    }
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

MemoryObject *LocalExecutor::injectMemory(ExecutionState &state,
                                          void *addr,
                                          const std::vector<unsigned char> &data,
                                          const string &type_desc,
                                          MemKind kind,
                                          const std::string &name,
                                          unsigned count) {

  size_t size = data.size();
  Type *type = kmodule->getEquivalentType(type_desc);
  size_t align;
  if (type != nullptr) {
    align = kmodule->targetData->getPrefTypeAlignment(type);
  } else {
    LLVMContext &ctx = kmodule->module->getContext();
    align = kmodule->targetData->getPrefTypeAlignment(Type::getInt32Ty(ctx));
  }

  MemoryObject *mo = memory->inject(addr, size, type, kind, align);
  if (mo != nullptr) {
    mo->name = name;
    mo->count = count;
    mo->created_size = size;
    ObjectState *os = bindObjectInState(state, mo);
    for (size_t idx = 0, end = data.size(); idx < end; ++idx) {
      os->write8(idx, data[idx]);
    }
    os->clearWritten();
  }
  return mo;
}

bool LocalExecutor::allocSymbolic(ExecutionState &state,
                                  Type *type,
                                  const llvm::Value *allocSite,
                                  MemKind kind,
                                  const std::string &name,
                                  WObjectPair &wop,
                                  size_t align,
                                  unsigned count) {

  wop.first = nullptr;
  wop.second = nullptr;
  // empty symolic name is rather pointless
  if (!name.empty()) {
    MemoryObject *mo = allocMemory(state, type, allocSite, kind, name, align, count);
    if (mo != nullptr) {
      ObjectState *os = makeSymbolic(state, mo);
      if (os != nullptr) {
        wop.first = mo;
        wop.second = os;
        return true;
      }
      delete mo;
    }
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

bool LocalExecutor::isMainEntry(const llvm::Function *fn) const {

  // check if this is the user main function
  if ((fn != nullptr) && (interpreterOpts.userMain == fn)) {

    // must return an integer
    if (fn->getReturnType()->isIntegerTy()) {

      // accept two arguments
      const auto &args = fn->getArgumentList();
      if (args.size() == 2) {

        // first arg must be an int
        const auto &argc = args.front();
        if (argc.getType()->isIntegerTy()) {

          // second arg must be a char**
          const auto &argv = args.back();
          const Type *argv_type = argv.getType();
          if (argv_type->isPointerTy()) {
            argv_type = argv_type->getPointerElementType();
            if (argv_type->isPointerTy()) {
              argv_type = argv_type->getPointerElementType();
              if (argv_type->isIntegerTy(8))
                // this is it!
                return true;
            }
          }
        }
      }
    }
  }
  return false;
}

void LocalExecutor::unconstrainGlobals(ExecutionState &state, Function *fn) {

  string fn_name = fn->getName();
  for (auto itr = kmodule->module->global_begin(), end = kmodule->module->global_end(); itr != end; ++itr) {
    GlobalVariable *v = itr;
    if (kmodule->isUserGlobal(v) && v->hasName()) {
      string gv_name = v->getName().str();
      if (v->isConstant() || v->hasHiddenVisibility())  continue; // next global

      auto pos = gv_name.find('.');
      // if dot in first position or the prefix does not equal the function name, continue to next variable
      if (pos == 0) continue;
      if (pos != string::npos && (fn_name != gv_name.substr(0, pos))) continue;

      MemoryObject *mo = globalObjects.find(v)->second;
      if (mo != nullptr) {

        if (interpreterOpts.verbose) {
          outs() << "unconstraining: " << gv_name << '\n';
        }

        // global may already have a value in this state. if so unlink it.
        const ObjectState *os = state.addressSpace.findObject(mo);
        if (os != nullptr) {
          state.addressSpace.unbindObject(mo);
        }
        makeSymbolic(state, mo);
      }
    }
  }
}

void LocalExecutor::bindModule(KModule *kmodule) {

  Executor::bindModule(kmodule);

  specialFunctionHandler->setLocalExecutor(this);
  sysModel = new SystemModel(this, optsModel);

  // prepare a generic initial state
  baseState = new ExecutionState();
  baseState->maxLoopIteration = maxLoopIteration;
  baseState->lazyAllocationCount = lazyAllocationCount;
  baseState->maxLazyDepth = maxLazyDepth;
  baseState->maxLoopForks = maxLoopForks;

  initializeGlobals(*baseState, interpreterOpts.test_objs);
  bindModuleConstants();

  // look for a libc initializer, execute if found to initialize the base state
  Function *libc_init = kmodule->module->getFunction("__uClibc_init");
  if (libc_init != nullptr) {
    KFunction *kf_init = kmodule->functionMap[libc_init];
    ExecutionState *state = new ExecutionState(*baseState, kf_init, libc_init->getName());
    if (statsTracker) statsTracker->framePushed(*state, nullptr);
    ExecutionState *initState = runLibCInitializer(*state, libc_init);
    if (initState != nullptr) {
      initState->addressSpace.clearWritten();
      delete baseState;
      baseState = initState;
    }
  }
  baseState->last_ret_value = nullptr;
  interpreterHandler->onStateInitialize(*baseState);
}

void LocalExecutor::bindModuleConstants() {

  if (kmodule->constantTable == nullptr) {
    kmodule->constantTable = new Cell[kmodule->constants.size()];
  }

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

// use for input generation
void LocalExecutor::runFunctionUnconstrained(Function *fn) {

  assert(interpreterOpts.mode == ExecModeID::igen);

  KFunction *kf = kmodule->functionMap[fn];
  if (kf == nullptr) {
    // not in this compilation unit
    return;
  }

  std::string name = fn->getName();
  faulting_state_stash.clear();
  std::vector<ExecutionState*> init_states;

  // useful values for later
  // get some common types we are going to need later
  LLVMContext &ctx = kmodule->module->getContext();
  Type *char_type = Type::getInt8Ty(ctx);
  size_t char_align = kmodule->targetData->getPrefTypeAlignment(char_type);
  Type *str_type = Type::getInt8PtrTy(ctx);
  size_t str_align = kmodule->targetData->getPrefTypeAlignment(str_type);

  unsigned ptr_width =  Context::get().getPointerWidth();

  WObjectPair wopStdIn;
  if (!allocSymbolic(*baseState, char_type, fn, MemKind::external, "#stdin_buff", wopStdIn, char_align, LEN_CMDLINE_ARGS + 1)) {
    klee_error("failed to allocate symbolic stdin_buff");
  }
  moStdInBuff = wopStdIn.first;

  // iterate through each phase of unconstrained progression
  for (auto itr = progression.begin(), end = progression.end(); itr != end; ++itr) {

    const auto &desc = *itr;

    // initialize a common initial state
    ExecutionState *state = new ExecutionState(*baseState, kf, name);
    if (statsTracker) statsTracker->framePushed(*state, nullptr);

    timeout = desc.timeout;
    unconstraintFlags |= desc.unconstraintFlags;

    // are we treating this fn as main?
    bool is_main = isMainEntry(fn);

    // unconstrain global state
    if (unconstraintFlags.isUnconstrainGlobals() || !is_main) {
      unconstrainGlobals(*state, fn);
    }

    // create parameter values
    // if this is main, special case the argument construction
    if (is_main) {

      // symbolic argc, symbolic argv,
      assert(fn->getArgumentList().size() == 2);

      init_states.clear();
      init_states.resize(SymArgs + 1);

      // push the module name into the state
      std::string md_name = kmodule->getModuleIdentifier();

      WObjectPair wopProgName;
      if (!allocSymbolic(*state, char_type, fn, MemKind::param, "#program_name", wopProgName, char_align, md_name.size() + 1)) {
        klee_error("failed to allocate symbolic argv_array");
      }
      MemoryObject *moProgName = wopProgName.first;
      ObjectState *osProgName = wopProgName.second;

      for (unsigned idx = 0, end = md_name.size(); idx < end; ++idx) {
        char ch = md_name[idx];
        addConstraint(*state, EqExpr::create(osProgName->read8(idx), ConstantExpr::create(ch, Expr::Int8)));
      }
      // null terminate the string
      addConstraint(*state, EqExpr::create(osProgName->read8(md_name.size()), ConstantExpr::create(0, Expr::Int8)));

      // get an array for the argv pointers
      WObjectPair wopArgv_array;
      if (!allocSymbolic(*state, str_type, fn, MemKind::param, "argv_array", wopArgv_array, str_align, SymArgs + 2)) {
        klee_error("failed to allocate symbolic argv_array");
      }

      // argv[0] -> binary name
      // argv[1 .. SymArgs] = symbolic value
      // argv[SymArgs] = null

      // despite being symbolic, argv[0] always points to program name
      addConstraint(*state, EqExpr::create(wopArgv_array.second->read(0, ptr_width), moProgName->getBaseExpr()));

      // allocate the command line arg strings for each starting state
      init_states[0] = state;
      for (unsigned index = 1; index <= SymArgs; index++) {

        ExecutionState *prev = init_states[index - 1];
        ExecutionState *curr = init_states[index] = new ExecutionState(*prev);

        WObjectPair wopArgv_body;
        std::string argName = "argv_" + itostr(index);
        if (!allocSymbolic(*curr, char_type, fn, MemKind::param, argName.c_str(), wopArgv_body, char_align, LEN_CMDLINE_ARGS + 1)) {
          klee_error("failed to allocate symbolic command line arg");
        }

        // constrain strings to command line strings, i.e.
        // [0] must be printable
        // [ 1 .. N] must be printable or '\0'
        // [N + 1] must be '\0'
        for (unsigned idx = 0; idx < LEN_CMDLINE_ARGS; ++idx) {
          ref<Expr> ch = wopArgv_body.second->read8(idx);
          ref<Expr> gt = SgeExpr::create(ch, ConstantExpr::create(0x20, Expr::Int8));
          ref<Expr> lt = SleExpr::create(ch, ConstantExpr::create(0x7e, Expr::Int8));
          ref<Expr> printable = AndExpr::create(gt, lt);
          ref<Expr> cmd = printable;
          if (index > 0) {
            cmd = OrExpr::create(printable, EqExpr::create(ch, ConstantExpr::create(0, Expr::Int8)));
          }
          addConstraint(*curr, cmd);
        }
        addConstraint(*curr, EqExpr::create(wopArgv_body.second->read8(LEN_CMDLINE_ARGS), ConstantExpr::create(0, Expr::Int8)));

        // and constrain pointer in argv array to point to body
        ref<Expr> ptr = wopArgv_array.second->read((ptr_width / 8) * (index), ptr_width);
        addConstraint(*curr, EqExpr::create(ptr, wopArgv_body.first->getBaseExpr()));
      }

      for (unsigned idx1 = 0; idx1 <= SymArgs; ++idx1) {
        // for each state constrain argc
        ExecutionState *curr = init_states[idx1];

        // and the remainder of the argv array should be null
        for (unsigned idx2 = idx1; idx2 <= SymArgs; ++idx2) {
          ref<Expr> ptr = wopArgv_array.second->read((ptr_width / 8) * (idx2 + 1), ptr_width);
          addConstraint(*curr, EqExpr::create(ptr, ConstantExpr::createPointer(0)));
        }
        ref<Expr> eArgC = ConstantExpr::create(idx1 + 1, Expr::Int32);
        ref<Expr> eArgV = ConstantExpr::createPointer(wopArgv_array.first->address);
        bindArgument(kf, 0, *curr, eArgC);
        bindArgument(kf, 1, *curr, eArgV);
        curr->arguments.clear();
        curr->arguments.push_back(eArgC);
        curr->arguments.push_back(eArgV);
      }

    } else {

      unsigned index = 0;
      state->arguments.reserve(fn->arg_size());
      for (Function::const_arg_iterator ai = fn->arg_begin(), ae = fn->arg_end(); ai != ae; ++ai, ++index) {

        const Argument &arg = *ai;
        std::string argName = arg.getName();
        Type *argType = arg.getType();
        size_t argAlign = arg.getParamAlignment();

        WObjectPair wop;
        if (!allocSymbolic(*state, argType, &arg, MemKind::param, argName, wop, argAlign)) {
          klee_error("failed to allocate symbolic function parameter");
        }
        ref<Expr> eArg = wop.second->read(0, kmodule->targetData->getTypeStoreSizeInBits(argType));
        bindArgument(kf, index, *state, eArg);
        state->arguments.push_back(eArg);
      }
      init_states.push_back(state);
    }

    outs() << fn->getName().str() << ": " << to_string(unconstraintFlags) << '\n';
    outs().flush();

    runFn(kf, init_states);
  }
  outs() << name << ": generated " << interpreterHandler->getNumTestCases() << " test case(s)\n";
}

void LocalExecutor::runFunctionAsMain(Function *f, int argc, char **argv, char **envp) {
  assert(false && "deprecated runFunctionAsMain (see runFunctionUnconstrained)");
}

// Used to replay a persisted test case
void LocalExecutor::runFunctionTestCase(const TestCase &test) {

  assert(interpreterOpts.mode == ExecModeID::rply);

  Function *fn = kmodule->module->getFunction(test.entry_fn);
  if (fn == nullptr) return;
  KFunction *kf = kmodule->functionMap[fn];
  if (kf == nullptr) return;

  faulting_state_stash.clear();

  // reverse the stdin data.  then we can pop data from end
  size_t stdin_size = test.stdin_buffer.size();
  if (stdin_size > 1) {
    baseState->stdin_buffer.resize(stdin_size);
    reverse_copy(test.stdin_buffer.begin(), test.stdin_buffer.end(), baseState->stdin_buffer.begin());
  } else {
    baseState->stdin_buffer = test.stdin_buffer;
  }

  // inject the test case memory objects into the replay state
  for (const auto &obj : test.objects) {

    MemKind kind = (MemKind) obj.kind;
    switch (kind) {
      // inject parameters and lazily initialized memory blobs
      case MemKind::alloca_l:
      case MemKind::external:
      case MemKind::heap:
      case MemKind::param:
      case MemKind::lazy: {
        injectMemory(*baseState, (void *) obj.addr, obj.data, obj.type, kind, obj.name, obj.count);
        break;
      }

      case MemKind::global: {
        // globals should already be injected, unless it is no longer a global
        auto pr = baseState->addressSpace.findMemoryObjectByName(obj.name, kind);
        if (pr.first == nullptr) {
          injectMemory(*baseState, (void *) obj.addr, obj.data, obj.type, kind, obj.name, obj.count);
        }
        break;
      }
      default: {
        outs() << "RLR: what to do with kind: " << to_string(kind) << '\n';
        break;
      }
    }
  }

  ExecutionState *state = new ExecutionState(*baseState, kf, test.entry_fn);
  if (statsTracker) statsTracker->framePushed(*state, nullptr);

  if (fn->arg_size() > test.arguments.size()) {
    errs() << "Insufficient number of arguments in test case\n";
    return;
  }

  unsigned idx = 0;
  for (auto itr = fn->arg_begin(), end = fn->arg_end(); itr != end; ++itr) {
    const Argument &arg = *itr;
    Expr::Width w = getWidthForLLVMType(arg.getType());
    ref<Expr> e = ConstantExpr::create(test.arguments[idx], w);
    bindArgument(kf, idx, *state, e);
    idx++;
  }

  std::vector<ExecutionState*> init_states = { state };
  runFn(kf, init_states);
}

void LocalExecutor::runMainConcrete(Function *fn,
                                    const vector<string> &args,
                                    const vector<unsigned char> &stdin_buffer,
                                    Function *at) {

  assert(interpreterOpts.mode == ExecModeID::irec);

  KFunction *kf = kmodule->functionMap[fn];
  if (kf == nullptr) {
    // not in this compilation unit
    return;
  }

  faulting_state_stash.clear();

  ExecutionState *state = new ExecutionState(*baseState, kf, fn->getName());
  if (statsTracker) statsTracker->framePushed(*state, nullptr);

  if (fn->arg_size() == 2) {

    unsigned ptr_width =  Context::get().getPointerWidth();
    assert(ptr_width == 64 && "64-bit only");

    ref<Expr> eArgC = ConstantExpr::create(args.size(), Expr::Int32);
    bindArgument(kf, 0, *state, eArgC);

    Type *str_type = Type::getInt8PtrTy(kmodule->module->getContext());
    size_t align = kmodule->targetData->getPrefTypeAlignment(str_type);

    vector<uint64_t> moArgStrs;
    moArgStrs.reserve(args.size() + 1);
    unsigned idx = 0;
    for (const string &arg : args) {
      const char *str = arg.c_str();
      unsigned len = arg.size() + 1;
      MemoryObject *mo = addExternalObject(*state, str, len, str_type, fn, align);
      mo->name = "*arg" + itostr(idx++);
      moArgStrs.push_back(mo->address);
    }
    moArgStrs.push_back(0);

    Type *v_type = str_type->getPointerTo(0);
    align = kmodule->targetData->getPrefTypeAlignment(v_type);
    MemoryObject *moArgv = addExternalObject(*state, moArgStrs.data(), moArgStrs.size() * sizeof(uint64_t), v_type, fn, align);
    moArgv->name = "*argV";
    ref<Expr> eArgV = ConstantExpr::createPointer(moArgv->address);
    bindArgument(kf, 1, *state, eArgV);

    // now load stdin, if specified
    size_t stdin_size = stdin_buffer.size();
    if (stdin_size > 1) {
      state->stdin_buffer.resize(stdin_size);
      reverse_copy(stdin_buffer.begin(), stdin_buffer.end(), state->stdin_buffer.begin());
    } else {
      state->stdin_buffer = stdin_buffer;
    }

    if (fn == at) {
      state->status = StateStatus::Snapshot;
      state->arguments.clear();
      state->arguments.push_back(eArgC);
      state->arguments.push_back(eArgV);
      interpreterHandler->processTestCase(*state);
    } else {
      std::vector<ExecutionState *> init_states = {state};
      runFn(kf, init_states);
    }
  }
}

void LocalExecutor::runFn(KFunction *kf, std::vector<ExecutionState*> &init_states) {

  assert(!init_states.empty());

  // Delay init till now so that ticks don't accrue during
  // optimization and such.
  initTimers();
  const BasicBlock *fn_entry = &kf->function->getEntryBlock();
  unsigned entry = kf->basicBlockEntry[const_cast<BasicBlock*>(fn_entry)];

  // initialize the starting set of initial states
  assert(states.empty());
  assert(addedStates.empty());
  assert(removedStates.empty());

  ExecutionState *root_state = nullptr;
  for (unsigned idx = 0, end = init_states.size(); idx < end; idx++) {
    ExecutionState *state = new ExecutionState(*init_states[idx]);
    if (idx == 0) {
      root_state = state;
      processTree = new PTree(root_state);
      root_state->ptreeNode = processTree->root;
    } else {
      assert(root_state != nullptr);
      root_state->ptreeNode->data = nullptr;
      std::pair<PTree::Node*, PTree::Node*> result = processTree->split(root_state->ptreeNode, root_state, state);
      root_state->ptreeNode = result.first;
      state->ptreeNode = result.second;
    }

//    StackFrame &sf = state->stack.back();
//    for (auto itr = loops.rbegin(), end = loops.rend(); itr != end; ++itr) {
//      sf.loopFrames.emplace_back(LoopFrame(*itr));
//    }
    state->pc = &kf->instructions[entry];
    addedStates.push_back(state);
  }

  if (interpreterOpts.mode == ExecModeID::igen) {
    searcher = constructUserSearcher(*this);
  } else {
    searcher = new DFSSearcher();
  }

  updateStates(nullptr);

  MonotonicTimer timer;
  const unsigned tid_timeout = 1;
  const unsigned tid_heartbeat = 2;

  // parse out the breakat lines
  break_fns.clear();
  break_lines.clear();
  if (BreakAt.size() > 0) {
    vector<string> lines;
    boost::algorithm::split(lines, BreakAt, boost::algorithm::is_any_of(","), boost::algorithm::token_compress_on);
    for (const string &line : lines) {
      if (!line.empty()) {
        if (isdigit(line.front())) {
          break_lines.insert(stoul(line));
        } else if (const Function *fn = kmodule->module->getFunction(line)) {
          break_fns.insert(fn);
        } else {
          ostringstream ss;
          ss << "break at element " << line << " not found";
          log_warning(ss);
        }
      }
    }
  }

  // if trace type is not defined here, then use the default from the module
  trace_type = interpreterOpts.trace;

  if (trace_type == TraceType::invalid) {
    trace_type = kmodule->getModuleTraceType();
  }

  if (trace_type == TraceType::bblocks) {
    tracer = new BBlocksTracer(kmodule);
  } else if (trace_type == TraceType::assembly) {
    tracer = new AssemblyTracer;
  } else if (trace_type == TraceType::statements) {
    tracer = new StatementTracer;
  } else if (trace_type == TraceType::calls) {
    tracer = new CallTracer(kmodule);
  }

  if (timeout > 0) timer.set(tid_timeout, timeout);
  timer.set(tid_heartbeat, HEARTBEAT_INTERVAL);

  HaltReason halt = HaltReason::OK;
  enable_state_switching = true;

  ExecutionState *state = nullptr;
  while (!states.empty() && !haltExecution && halt == HaltReason::OK) {

    if (enable_state_switching || state == nullptr || states.find(state) == states.end()) {
      state = &searcher->selectState();
    }

    assert(!doConcreteInterpretation || states.size() == 1);

    KInstruction *ki = state->pc;
    stepInstruction(*state);

    if (tracer != nullptr) {
      tracer->append_instr(state->trace, ki);
    }

    try {
      if (!state->trace.empty() && break_lines.find(state->trace.back()) != break_lines.end()) {
        outs() << "break at " << state->trace.back() << '\n';
#ifdef _DEBUG
        enable_state_switching = false;
#endif
      }
      executeInstruction(*state, ki);

    } catch (bad_expression &e) {
      terminateState(*state, "uninitialized expression");
    } catch (solver_failure &e) {
      terminateState(*state, "solver failure");
    }
    processTimers(state, 0);
    updateStates(state);

    // check for expired timers
    unsigned expired = timer.expired();
    if (expired == tid_timeout) {
#ifdef _DEBUG
      if (enable_state_switching) halt = HaltReason::TimeOut;
#else
      halt = HaltReason::TimeOut;
#endif
    } else if (expired == tid_heartbeat) {
      interpreterHandler->resetWatchDogTimer();
      timer.set(tid_heartbeat, HEARTBEAT_INTERVAL);
    }
    if (!doConcreteInterpretation) checkMemoryUsage();
  }

  loopForkCounter.clear();
  for (ExecutionState *state : states) {
    terminateStateEarly(*state, "flushing states on halt");
  }
  updateStates(nullptr);
  assert(states.empty());

  if (tracer != nullptr) {
    delete tracer;
    tracer = nullptr;
  }

  delete searcher;
  searcher = nullptr;

  delete processTree;
  processTree = nullptr;

  // clean up our initial states
  for (auto state : init_states) {
    delete state;
  }
  init_states.clear();

  // RLR TODO: now consider our stashed faulting states?
  faulting_state_stash.clear();

  // RLR TODO: save pending states as well...
}

ExecutionState *LocalExecutor::runLibCInitializer(klee::ExecutionState &init_state, llvm::Function *initializer) {

  ExecutionState *result = nullptr;

  KFunction *kf = kmodule->functionMap[initializer];
  unsigned entry = kf->basicBlockEntry[&initializer->getEntryBlock()];
  init_state.pc = &kf->instructions[entry];

  processTree = new PTree(&init_state);
  init_state.ptreeNode = processTree->root;

  states.insert(&init_state);

  searcher = new DFSSearcher();
  std::vector<ExecutionState *> newStates(states.begin(), states.end());
  searcher->update(nullptr, newStates, std::vector<ExecutionState *>());
  libc_initializing = true;

  while (libc_initializing && !states.empty()) {

    ExecutionState *state = &searcher->selectState();
    KInstruction *ki = state->pc;
    stepInstruction(*state);

    try {
      executeInstruction(*state, ki);
    } catch (bad_expression &e) {
      outs() << "    * uninitialized expression, restarting execution\n";
      outs().flush();
    } catch (solver_failure &e) {
      outs() << "solver failure\n";
      outs().flush();
    }
    processTimers(state, 0);
    updateStates(state);
  }

  loopForkCounter.clear();

  // libc initializer should not have forked any additional states
  if (states.size() > 1) {
    klee_error("libc initialization spawned multiple states");
  }
  if (states.empty()) {
    klee_error("libc initialization failed to yield a valid state");
  } else {
    result = *states.begin();
    states.clear();
  }
  updateStates(nullptr);

  // cleanup
  delete searcher;
  searcher = nullptr;

  delete processTree;
  processTree = nullptr;
  result->popFrame();
  return result;
}

void LocalExecutor::terminateState(ExecutionState &state, const string &message) {

  if (!message.empty()) state.messages.push_back(message);
  if (state.status == StateStatus::Completed    ||
     (state.status == StateStatus::Error) ||
     (interpreterOpts.mode != ExecModeID::igen && state.status == StateStatus::MemFaulted) ||
     (SavePendingStates && state.status == StateStatus::Incomplete) ) {
    interpreterHandler->processTestCase(state);
  } else {
    // ??
  }
  interpreterHandler->onStateFinalize(state);
  Executor::terminateState(state, message);
}

void LocalExecutor::terminateStateOnExit(ExecutionState &state) {
  state.status = StateStatus::Completed;
  Executor::terminateStateOnExit(state);
}

void LocalExecutor::terminateStateOnMemFault(ExecutionState &state, const KInstruction *ki, const std::string &message) {
  state.status = StateStatus::MemFaulted;
  state.instFaulting = ki;
  terminateState(state, message);
}

void LocalExecutor::terminateStateEarly(ExecutionState &state, const string &message) {
  state.status = StateStatus::Incomplete;
  Executor::terminateStateEarly(state, message);
}

void LocalExecutor::terminateStateOnError(ExecutionState &state, TerminateReason termReason, const string &message) {
  state.status = StateStatus::Error;
  Executor::terminateStateOnError(state, termReason, message);
}

void LocalExecutor::terminateStateOnDecimated(ExecutionState &state) {
  state.status = StateStatus::Decimated;
  terminateState(state, "decimated");
}

void LocalExecutor::terminateStateOnDiscard(ExecutionState &state) {
  state.status = StateStatus::Discarded;
  terminateState(state, "discarded");
}

void LocalExecutor::checkMemoryUsage() {

  Executor::checkMemoryUsage();

  // expensive, so do not do this very often
  if ((maxStatesInLoop > 0) && (stats::instructions % 0xFFF) == 0) {
    vector<const Loop*> too_many;
    for (auto &pr : loopStateCounter) {
      if (pr.second > maxStatesInLoop) {
        too_many.push_back(pr.first);
      }
    }
    for (const auto *loop : too_many) {
      decimateStatesInLoop(loop, 99);
    }
  }
}

unsigned LocalExecutor::decimateStatesInLoop(const Loop *loop, unsigned skip_counter) {

  unsigned killed = 0;
  unsigned counter = 0;
  skip_counter++;
  for (ExecutionState *state : states) {
    for (const auto &sf : state->stack) {
      for (const auto lf : sf.loopFrames) {
        if ((lf.loop == loop) && (++counter % skip_counter != 0)) {
          state->status = StateStatus::Decimated;
          terminateStateOnDecimated(*state);
          killed++;
        }
      }
    }
  }
  return killed;
}

unsigned LocalExecutor::numStatesInLoop(const Loop *loop) const {

  auto itr = loopStateCounter.find(loop);
  if (itr != loopStateCounter.end()) {
    return itr->second;
  }
  return 0;
}

ref<ConstantExpr> LocalExecutor::ensureUnique(ExecutionState &state, const ref<Expr> &e) {

  ref<ConstantExpr> result;
  if (isa<ConstantExpr>(e)) {
    result = cast<ConstantExpr>(e);
  } else {
    if (solver->getValue(state, e, result)) {
      ref<Expr> eq = EqExpr::create(e, result);
      if (!solver->mustBeTrue(state, eq)) {
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
    if (solver->getValue(state, e, value)) {
      ref<Expr> eq = EqExpr::create(e, value);
      result = solver->mustBeTrue(state, eq);
    }
  }
  return result;
}

void LocalExecutor::transferToBasicBlock(ExecutionState &state, llvm::BasicBlock *src, llvm::BasicBlock *dst) {

  if ((!libc_initializing) && (dst->getParent() == src->getParent())) {

    // update the loop frame
    StackFrame &sf = state.stack.back();
    KFunction *kf = sf.kf;
    const llvm::Loop *src_loop = kf->kloop.getLoopFor(src);
    const llvm::Loop *dst_loop = kf->kloop.getLoopFor(dst);

    if (src_loop == dst_loop) {
      // either source and destination are not in a loop,
      // or they are in the same loop
      if (dst_loop != nullptr) {

        // both in a loop, if the dest is the loop header, then we have completed a cycle
        if ((dst_loop->getHeader() == dst) && !sf.loopFrames.empty()) {
          LoopFrame &lf = sf.loopFrames.back();
          if (lf.loop == dst_loop) lf.counter += 1;
        }
      }
    } else {

      // source and destination loop are different
      // we either entered a new loop, or exited the previous loop (or both?)
      if (src_loop == nullptr) {

        // entered the first loop
        assert(sf.loopFrames.empty());
        sf.loopFrames.emplace_back(LoopFrame(dst_loop, loopStateCounter));
      } else if (dst_loop == nullptr) {

        // left the last loop
        sf.loopFrames.pop_back();
        assert(sf.loopFrames.empty());
      } else {
        // neither empty implies we just transitioned up/down nested loops
        if (src_loop->contains(dst_loop)) {

          // create frames for each intermediate loop
          const llvm::Loop *curr = dst_loop;
          std::vector<const llvm::Loop *> loops;
          while (curr != src_loop) {
            loops.push_back(curr);
            curr = curr->getParentLoop();
          }
          for (auto itr = loops.rbegin(), end = loops.rend(); itr != end; ++itr) {
            sf.loopFrames.emplace_back(LoopFrame(*itr, loopStateCounter));
          }

        } else {
          assert(dst_loop->contains(src_loop));

          // pop loops from frame until we get to the source
          const llvm::Loop *prior = nullptr;
          while (!sf.loopFrames.empty() && (prior != src_loop)) {
            prior = sf.loopFrames.back().loop;
            sf.loopFrames.pop_back();
          }
        }
      }
    }
  }
  Executor::transferToBasicBlock(state, src, dst);
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

      if (bi->isUnconditional()) {
        BasicBlock *dst = bi->getSuccessor(0);
        transferToBasicBlock(state, src, dst);

      } else {
        // FIXME: Find a way that we don't have this hidden dependency.
        assert(bi->getCondition() == bi->getOperand(0) && "Wrong operand index!");
        const KFunction *kf = kmodule->functionMap[src->getParent()];
        state.allBranchCounter++;
        ref<Expr> cond = eval(ki, 0, state).value;

        Executor::StatePair branches = fork(state, cond, false);

        // NOTE: There is a hidden dependency here, markBranchVisited
        // requires that we still be in the context of the branch
        // instruction (it reuses its statistic id). Should be cleaned
        // up with convenient instruction specific data.
        if (statsTracker && kf->trackCoverage)
          statsTracker->markBranchVisited(branches.first, branches.second);

        ExecutionState *states[2] = { branches.first, branches.second };
        bool bothSatisfyable = (states[0] != nullptr) && (states[1] != nullptr);

        for (unsigned index = 0; index < countof(states); ++index) {
          if (states[index] != nullptr) {

            BasicBlock *dst = bi->getSuccessor(index);
            transferToBasicBlock(*states[index], src, dst);

            if (!doConcreteInterpretation && bothSatisfyable) {
              states[index]->unconBranchCounter++;
              StackFrame &sf = states[index]->stack.back();
              if (!sf.loopFrames.empty()) {

                LoopFrame &lf = sf.loopFrames.back();
                ++loopForkCounter[lf.loop];
                if (lf.loop->isLoopExiting(src) && lf.loop->contains(dst)) {
                  if (lf.counter > maxLoopIteration && loopForkCounter[lf.loop] > maxLoopForks){

                    // finally consider terminating the state.
                    terminateState(*states[index], "loop throttled");
                  }
                }
              }
            }
          }
        }
      }
      break;
    }

    case Instruction::Ret: {
      if (libc_initializing &&
          ((state.stack.size() == 0 || !state.stack.back().caller))) {
        libc_initializing = false;
      } else {
        KFunction *ret_from = state.stack.back().kf;
        if (tracer != nullptr) {
          tracer->append_return(state.trace, ret_from);
        }
        if (state.stack.size() > 0 && ret_from->function->hasFnAttribute(Attribute::NoReturn)) {
          // this state completed
          state.last_ret_value = nullptr;
          terminateStateOnExit(state);
        } else {
          Executor::executeInstruction(state, ki);
        }
        if ((state.status != StateStatus::Completed) && kmodule->isUserFunction(ret_from->function)) {
          interpreterHandler->onStateUserFunctionReturn(state);
        }
      }
      break;
    }

    case Instruction::Invoke:
    case Instruction::Call: {

      const CallSite cs(i);
      Function *fn = getTargetFunction(cs.getCalledValue(), state);
      if (fn != nullptr) {
        string fn_name = fn->getName();
        interpreterHandler->incCallCounter(fn);

        if (break_fns.find(fn) != break_fns.end()) {
          outs() << "break at " << fn->getName() << '\n';
#ifdef _DEBUG
          enable_state_switching = false;
#endif
        }

        if (interpreterOpts.mode == ExecModeID::irec && interpreterOpts.userSnapshot == fn) {
          state.status = StateStatus::Snapshot;
          state.instFaulting = ki;
          unsigned numArgs = cs.arg_size();

          // evaluate arguments
          state.arguments.reserve(numArgs);
          for (unsigned idx = 0; idx < numArgs; ++idx) {
            ref<Expr> e = eval(ki, idx + 1, state).value;
            state.arguments.push_back(toUnique(state, e));
          }

          interpreterHandler->processTestCase(state);
          terminateState(state, "snapshot");
          return;
        }

        // invoke model of posix functions
        if (sysModel != nullptr) {
          ref<Expr> retExpr;
          if (sysModel->Execute(state, fn, ki, cs, retExpr)) {
            // the system model handled the call
            if (!retExpr.isNull()) {
              // and return a result
              bindLocal(ki, state, retExpr);
            }
            return;
          }
        }

        if (libc_initializing || kmodule->isInternalFunction(fn)) {
          Executor::executeInstruction(state, ki);
          return;
        }

        assert(fn->getIntrinsicID() == Intrinsic::not_intrinsic);
        if (tracer != nullptr) {
          tracer->append_call(state.trace, kmodule->getKFunction(fn));
        }

        if (!unconstraintFlags.isStubCallees()) {
          // we're performing the function call, if possible
          if (isLegalFunction(fn)) {
            Executor::executeInstruction(state, ki);
          } else {
            // direct callee with no body.  not good...
            stringstream ss;
            ss << "undefined callee: " << fn_name;
            terminateStateOnError(state, TerminateReason::External, ss.str());
          }

        } else {
          // inject an unconstraining stub
          assert(false && "should not happen in brt mode");
        }

      } else {

        // this is an indirect call (i.e. a through a function pointer)
        // try to convert function pointer to a constant value
        ref<Expr> callee = eval(ki, 0, state).value;
        callee = toUnique(state, callee);

        // evaluate arguments
        unsigned numArgs = cs.arg_size();
        std::vector< ref<Expr> > arguments;
        arguments.reserve(numArgs);

        for (unsigned j=0; j<numArgs; ++j) {
          ref<Expr> arg = eval(ki, j + 1, state).value;
          arguments.push_back(arg);
        }

        vector<Function*> targets;
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(callee)) {
          Function *fn = (Function*) CE->getZExtValue();
          if (isLegalFunction(fn)) {
            targets.push_back(fn);
          }
        } else {
          // enumerate all potential fn targets
          const FunctionType *fnType = dyn_cast<FunctionType>(cast<PointerType>(cs.getCalledValue()->getType())->getElementType());
          set<const Function*> fns;
          kmodule->getFnsOfType(fnType, fns);
          for (auto fn : fns) {
            if (isLegalFunction(fn)) {
              targets.push_back(const_cast<Function*>(fn));
            }
          }
        }

        unsigned num_targets = targets.size();
        if (num_targets == 0) {
          terminateStateOnError(state, TerminateReason::Ptr, "legal indirect callee not found");
        } else if (num_targets == 1) {
          if (tracer != nullptr) {
            tracer->append_call(state.trace, kmodule->getKFunction(targets.front()));
          }
          executeCall(state, ki, targets.front(), arguments);
        } else {
          // RLR TODO: general case, need to fork on multiple potential targets
          klee_error("general case of unconstrained fnptrs not implemented yet");
        }
      }

#if 0 == 1

      // if not stubbing callees and target is in the module
      if (!unconstraintFlags.isStubCallees() && isInModule) {
        if (noReturn) {
          terminateStateOnExit(state);
        } else {
          Executor::executeInstruction(state, ki);
        }
        return;
      }

      // either stubbed callees or target is not in the module
      if (noReturn) {
        terminateStateOnExit(state);
        return;
      }

      // we will be substituting an unconstraining stub subfunction.
      ostringstream ss;
      ss << "stubbing function " << fnName;
      log_warning(ss, state, ki);

      // hence, this is a function in this module
      unsigned counter = state.callTargetCounter[fnName]++;

      // consider the arguments pushed for the call, rather than
      // args expected by the target
      unsigned numArgs = cs.arg_size();
      if (fn == nullptr || !fn->isVarArg()) {
        for (unsigned index = 0; index < numArgs; ++index) {
          const Value *v = cs.getArgument(index);
          Type *argType = v->getType();

          if ((countLoadIndirection(argType) > 0) /* && !progInfo->isConstParam(fnName, index) */) {

            ref<Expr> exp_addr = eval(ki, index + 1, state).value;
            ObjectPair op;

            // find the referenced memory object
            if (resolveMO(state, exp_addr, op) == ResolveResult::OK) {
              const MemoryObject *orgMO = op.first;
              const ObjectState *orgOS = op.second;

              ref<Expr> e = orgOS->getBoundsCheckPointer(exp_addr);
              if (solver->mayBeTrue(state, e)) {
                addConstraint(state, e);

                ref<ConstantExpr> address = ensureUnique(state, exp_addr);
                ObjectState *argOS = state.addressSpace.getWriteable(orgMO, orgOS);
                Type *eleType = argType->getPointerElementType();
                unsigned eleSize;

                // reconsider LazyAllocationCount for fallback size here...
                if (eleType->isSized()) {
                  eleSize = (unsigned) kmodule->targetData->getTypeStoreSize(eleType);
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
      if (isInModule && unconstraintFlags.isUnconstrainGlobals()) {
        newUnconstrainedGlobalValues(state, fn, counter);
      }

      // now get the return type
      Type *ty = cs->getType();
      if (!ty->isVoidTy()) {

        WObjectPair wop;
        if (!allocSymbolic(state, ty, i, MemKind::output, fullName(fnName, counter, "0"), wop)) {
          klee_error("failed to allocate called function parameter");
        }
        Expr::Width width = kmodule->targetData->getTypeStoreSizeInBits(ty);
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

            // RLR TODO: this is only returning new objects.
            // should it also return existing objects?

            Type *base_type = ty->getPointerElementType();

            // LazyAllocationCount needs to be expanded for string and buffer types.
            unsigned count = LazyAllocationCount;
            if (base_type->isIntegerTy(8) && count < lazyStringLength) {
              count = lazyStringLength;
            }
            // finally, try with a new object
            WObjectPair wop;
            allocSymbolic(*sp.second, base_type, i, MemKind::lazy, fullName(fnName, counter, "*0"), wop, 0, count);
            ref<ConstantExpr> ptr = wop.first->getOffsetIntoExpr(LazyAllocationOffset * (wop.first->size / count));
            ref<Expr> eq = EqExpr::create(retExpr, ptr);
            addConstraint(*sp.second, eq);

            // insure strings are null-terminated
            if (base_type->isIntegerTy(8)) {
              addConstraint(*sp.second, EqExpr::create(wop.second->read8(count - 1), ConstantExpr::create(0, Expr::Int8)));
            }
          }
        }
      }
#endif
      break;
    }

    // Memory instructions...

    case Instruction::Alloca: {

      AllocaInst *ai = cast<AllocaInst>(i);

      unsigned size = (unsigned) kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
      unsigned count = 1;
      if (ai->isArrayAllocation()) {
        ref<Expr> cnt = eval(ki, 0, state).value;
        if (isa<ConstantExpr>(cnt)) {
          count = cast<ConstantExpr>(cnt)->getZExtValue();
        } else {
          assert(false && "non-const lallocation size");
        }
      }
      bool to_symbolic = false /*!libc_initializing && unconstraintFlags.isUnconstrainLocals() && !ai->getName().empty() */;
      executeSymbolicAlloc(state, size * count, count, ai->getAllocatedType(), MemKind::alloca_l, ki, to_symbolic);
      break;
    }

    case Instruction::GetElementPtr: {

      assert(i->getType()->isPtrOrPtrVectorTy());

      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
      ref<Expr> base = eval(ki, 0, state).value;
      // see if we can find a memory object containing base
      // if see, it may need lazy initializing.
      // if no object is found, then its not necessarily an error
      base = toUnique(state, base);

      if (isReadExpr(base) && isUnconstrainedPtr(state, base)) {

        string name = "#gepbase";
        Type *type = i->getType();
        if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(i)) {
          Value *v = gep->getPointerOperand();
          if (v->hasName()) name = v->getName().str();
          type = v->getType();
        }
        state.restartInstruction();
        expandLazyAllocation(state, base, type, ki, name, false);
        return;
      }

      ObjectPair op;
      ResolveResult result = resolveMO(state, base, op);
      if (result == ResolveResult::OK) {
        if ((op.first->type != nullptr) && op.first->type->isPointerTy()) {
          unsigned ptr_width =  Context::get().getPointerWidth();
          ref<Expr> ptr = op.second->read(0, ptr_width);
          ptr = toUnique(state, ptr);
          if (isReadExpr(ptr) && isUnconstrainedPtr(state, ptr)) {
            state.restartInstruction();

            string name = op.first->name + ":?";
            Type *type = i->getType();
            if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(i)) {
              Value *v = gep->getPointerOperand();
              type = v->getType();
            }
            // RLR TODO: need offset now to be more precise
            expandLazyAllocation(state, ptr, type, ki, name, false);
            return;
          }
        }
        // RLR TODO: where was this needed?  at least one of the benchmarks geps a null ptr in correct code
//      } else if (result == ResolveResult::NullAccess) {
//        // well, ..., that can't be good.
//        terminateState(state, "GEP from NULL base");
//        return;
      }

      for (auto itr = kgepi->indices.begin(), end = kgepi->indices.end(); itr != end; ++itr) {
        uint64_t elementSize = itr->second;
        ref<Expr> index = eval(ki, itr->first, state).value;
        base = AddExpr::create(base,
                               MulExpr::create(Expr::createSExtToPointerWidth(index),
                                               Expr::createPointer(elementSize)));
      }
      if (kgepi->offset) {
        base = AddExpr::create(base, Expr::createPointer(kgepi->offset));
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
      executeWriteMemoryOperation(state, base, value, ki, name);
      break;
    }

    case Instruction::IntToPtr: {
//      log_warning("Integer cast to pointer", state, ki);
      Executor::executeInstruction(state, ki);
      break;
    }
    case Instruction::PtrToInt: {
//      log_warning("Pointer cast to integer", state, ki);
      Executor::executeInstruction(state, ki);
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
            if (mo->isLazy() || mo->isHeap()) {

              // if lazy, make sure the new type fits...
              if (doAssumeInBounds && mo->isLazy()) {
                if (destSize > mo->size) {
                  // not even one will fit
                  log_warning("lazy init size too small for bitcast", state, ki);
                }

                // type aware allocation size
                destSize *= lazyAllocationCount;
                destSize = std::min(destSize, mo->size);
                if (destSize > os->visible_size) {
                  ObjectState *wos = state.addressSpace.getWriteable(mo, os);
                  wos->visible_size = destSize;
                }
              }

              // for lazy and heap, record pointed type change
              if (srcPtd != destPtd) {

                // only record if this is a pointer to the beginning of a memory object
                ref<Expr> is_zero = Expr::createIsZero(mo->getOffsetExpr(ptr));

                if (solver->mayBeTrue(state, is_zero)) {
                  ObjectState *wos = state.addressSpace.getWriteable(mo, os);
                  wos->types.insert(destTy);
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

    case Instruction::UDiv:  // all fall through
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::SRem: {
      ref<Expr> denom = eval(ki, 1, state).value;
      if (addConstraintOrTerminate(state, Expr::createIsNonZero(denom))) {
        Executor::executeInstruction(state, ki);
      }
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
      const MemoryObject *mo = sym.first;
//      const ObjectState *os = state->addressSpace.findObject(mo);

      std::string name = mo->name;
      const llvm::Type *type = mo->type;
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

bool LocalExecutor::getSymbolicSolution(const ExecutionState &state, std::vector<SymbolicSolution> &res, std::vector<ExprSolution> &exprs) {

  if (Executor::getSymbolicSolution(state, res)) {

    // if all expressions are (or can be resolved to) constants, then
    // no need to resort to the solver
    bool need_solver = false;
    for (auto itr = exprs.begin(), end = exprs.end(); itr != end; ++itr) {

      ref<Expr> e = toUnique(state, itr->first);
      itr->first = e;
      if (isa<ConstantExpr>(e)) {
        itr->second = cast<ConstantExpr>(e);
      } else {
        need_solver = true;
      }
    }
    if (need_solver) {

      // not all constant expressions.  need to get get values consistent with
      // the returned solution.
      std::vector<ref<Expr> > bindings;
      for (const auto &solution : res) {
        const MemoryObject *mo = solution.first;
        const vector<unsigned char> &value = solution.second;
        if (const Array *array = state.findSymbolic(mo)) {

          for (unsigned idx = 0, end = array->size; idx < end; ++idx) {
            unsigned char byte = value[idx];
            ref<Expr> e = EqExpr::create(ReadExpr::create(UpdateList(array, 0),
                                         ConstantExpr::alloc(idx, array->getDomain())),
                                         ConstantExpr::alloc(byte, array->getRange()));
            bindings.push_back(e);
          }
        }
      }
      ConstraintManager cm(bindings);
      for (auto itr = exprs.begin(), end = exprs.end(); itr != end; ++itr) {
        if (itr->second.isNull()) {
          solver->solver->getValue(Query(cm, itr->first), itr->second);
        }
      }
    }
    return true;
  }
  return false;
}

bool LocalExecutor::getConcreteSolution(ExecutionState &state,
                                        std::vector<SymbolicSolution> &result,
                                        const std::set<MemKind> &kinds) {

#if 0 == 1
  // RLR TODO: here be debug statements
  map<uint64_t,const MemoryObject*> addresses;
  for (auto obj : state.addressSpace.objects) {
    uint64_t addr = obj.first->address;
    addresses.insert(make_pair(obj.first->address, obj.first));
  }
  size_t size = addresses.size();
  for (auto pr : addresses) {
    uint64_t addr = pr.first;
    const MemoryObject *mo = pr.second;
    errs() << addr << ':' << mo << '\n';
  }
#endif

  // copy out all memory objects
  for (auto itr = state.addressSpace.objects.begin(), end = state.addressSpace.objects.end(); itr != end; ++itr) {
    const MemoryObject *mo = itr->first;
    if (kinds.find(mo->kind) != kinds.end()) {

      const ObjectState *os = itr->second;
      result.emplace_back(make_pair(mo, vector<unsigned char>{}));
      vector<unsigned char> &value = result.back().second;
      os->readConcrete(value);
    }
  }
  return true;
}

Interpreter *Interpreter::createLocal(LLVMContext &ctx,
                                      const InterpreterOptions &opts,
                                      InterpreterHandler *ih) {
  return new LocalExecutor(ctx, opts, ih);
}

}


///

