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
#include "klee/Internal/Support/Debug.h"

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
#include <llvm/IR/Intrinsics.h>
#include "llvm/Support/CallSite.h"

#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>

using namespace llvm;
using namespace std;
namespace fs=boost::filesystem;

namespace klee {

extern RNG theRNG;
struct InstructionInfo;

class bad_expression : public std::runtime_error
{
public:
  bad_expression() : std::runtime_error("null expression") {}
  bad_expression(const char *msg) : std::runtime_error(msg) {}
};


class Tracer {
  virtual unsigned to_entry(KInstruction *ki);
};

cl::opt<unsigned> SymArgsMax("sym-args-max", cl::init(4), cl::desc("Maximum number of command line arguments (only used when entry-point is main) (default=4)"));
cl::opt<unsigned> SymStdinSize("sym-stdin-size", cl::init(32), cl::desc("Number of bytes for symbolic reads (default=32)"));
cl::opt<unsigned> LazyAllocCount("lazy-alloc-count", cl::init(4), cl::desc("Number of items to lazy initialize pointer (default=4)"));
cl::opt<unsigned> LazyStringLength("lazy-string-length", cl::init(4), cl::desc("Number of characters to lazy initialize i8 ptr (default=4)"));
cl::opt<unsigned> LazyAllocOffset("lazy-alloc-offset", cl::init(0), cl::desc("index into lazy allocation to return (default=0)"));
cl::opt<unsigned> LazyAllocMinSize("lazy-alloc-minsize", cl::init(0), cl::desc("minimum size of a lazy allocation (default=0)"));
cl::opt<unsigned> LazyAllocDepth("lazy-alloc-depth", cl::init(4), cl::desc("Depth of items to lazy initialize pointer (default=4)"));
cl::opt<unsigned> LazyAllocExisting("lazy-alloc-existing", cl::init(2), cl::desc("number of lazy allocations to include existing memory objects of same type (default=2)"));
cl::opt<bool> LazyAllocNull("lazy-alloc-null", cl::init(true), cl::desc("do not lazy allocate to a null object (default=true)"));
cl::opt<string> BreakAt("break-at", cl::desc("break at the given trace line number or function name"));

LocalExecutor::LocalExecutor(LLVMContext &ctx, const InterpreterOptions &opts, InterpreterHandler *ih) :
  Executor(ctx, opts, ih),
  lazyAllocationCount(LazyAllocCount),
  lazyStringLength(LazyStringLength),
  maxLazyDepth(LazyAllocDepth),
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
      assert(opts.test_case != nullptr);
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

  if (statsTracker) {
    statsTracker->done();
  }
  if (baseState != nullptr) {
    delete baseState;
    baseState = nullptr;
  }
}

void LocalExecutor::shutdown() {

  if (sysModel != nullptr) {
    delete sysModel;
    sysModel = nullptr;
  }
  Executor::shutdown();
}

bool LocalExecutor::addConstraintOrTerminate(ExecutionState &state, ref<Expr> e) {

  if (solver->mayBeTrue(state, e)) {
    addConstraint(state, e);
    return true;
  }

  // NOTE: if this function returns false, state must not be accessed again
  terminateStateOnDispose(state, "added invalid constraint");
  return false;
}

LocalExecutor::ResolveResult LocalExecutor::resolveMO(ExecutionState &state, ref<Expr> address, ObjectPair &op) {

  assert(address.get()->getWidth() == Context::get().getPointerWidth());

  address = state.constraints.simplifyExpr(address);

  if (isa<ConstantExpr>(address)) {
    ref<ConstantExpr> caddress = cast<ConstantExpr>(address);
    if (caddress->getZExtValue() < 1024) {
      // close to zero anyway...
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

void LocalExecutor::executeAlloca(ExecutionState &state, unsigned size, unsigned count, const llvm::Type *type,
                                  KInstruction *target) {

  size_t allocationAlignment = getAllocationAlignment(target->inst);
  MemoryObject *mo = memory->allocate(size * count, type, MemKind::alloca_l, target->inst, allocationAlignment);
  if (mo == nullptr) {
    bindLocal(target, state, ConstantExpr::createPointer(0));
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
    bindLocal(target, state, mo->getBaseExpr());
  }
}

void LocalExecutor::executeAlloca(ExecutionState &state, unsigned size, ref<Expr> count, const llvm::Type *type,
                                  KInstruction *target) {

  ref<ConstantExpr> min_count = toConstantMin(state, count, "alloca");
  return executeAlloca(state, size, (unsigned) min_count->getZExtValue(), type, target);
}

void LocalExecutor::executeFree(ExecutionState &state,
                                ref<Expr> address,
                                KInstruction *target) {
  StatePair zeroPointer = fork(state, Expr::createIsZero(address), true);
  unsigned counter = 0;
  if (zeroPointer.first) {
    counter += 1;
    if (target)
      bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
  }
  if (zeroPointer.second) { // address != 0
    counter += 1;

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
  if (target && counter > 1) {
    frequent_forkers[target->info->assemblyLine] += (counter - 1);
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

void LocalExecutor::replayGlobalValues(ExecutionState &state, Function *fn, unsigned counter) {
  UNUSED(state);
  UNUSED(fn);
  UNUSED(counter);
}

bool LocalExecutor::executeReadMemoryOperation(ExecutionState &state, ref<Expr> address, const Type *type, KInstruction *target) {

  ObjectPair op;
  ResolveResult result = resolveMO(state, address, op);
  if (result != ResolveResult::OK) {
    // could not find an object, but op.first points to object before
    terminateStateOnMemFault(state, target, address, op.first, "read resolveMO");
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
      terminateStateOnMemFault(*currState, target, address, mo, "read OoB const offset");
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
      terminateStateOnMemFault(*currState, target, address, mo, "read OoB1 offset");
      if (sp.second != nullptr && sp.second != currState) {
        terminateStateOnMemFault(*sp.second, target, address, mo, "read OoB2 offset");
      }
      return false;

    } else {
      // inbound solution exists.  should continue as currState. sp.second must terminate
      currState = sp.first;
      if (sp.second != nullptr) {
        terminateStateOnMemFault(*sp.second, target, address, mo, "read OoB3 offset");
      }
    }
  }

  if (!doConcreteInterpretation && !currState->isSymbolic(mo) && !isLocallyAllocated(*currState, mo) && mo->isLazy()) {
    outs() << "RLR: Does this ever actually happen?\n";
    os = makeSymbolic(*currState, mo);
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
    expandLazyAllocation(state, e, type->getPointerElementType(), target, name, LazyAllocNull);
  }
  return true;
}

void LocalExecutor::expandLazyAllocation(ExecutionState &state, ref<Expr> addr, const llvm::Type *type, KInstruction *target,
                                         const std::string &name, bool allow_null) {

  assert(type->isPointerTy());

  Type *base_type = type->getPointerElementType();
  if (base_type->isFirstClassType()) {

    // count current depth of lazy allocations
    unsigned depth = 0;
    unsigned fork_counter = 0;
    for (auto end = (unsigned) name.size(); depth < end && name.at(depth) == '*'; ++depth);

    ref<ConstantExpr> null = Expr::createPointer(0);
    ref<Expr> eqNull = EqExpr::create(addr, null);

    if (depth >= maxLazyDepth) {

      if (allow_null) {
        // too deep. no more forking for this pointer.
        addConstraintOrTerminate(state, eqNull);
      } else {
        terminateStateOnDispose(state, "memory depth exceeded");
      }
      // must not touch state again in case of failure

    } else {

      ExecutionState *next_fork;
      if (allow_null) {
        StatePair sp = fork(state, eqNull, true);

        // in the true case, ptr is null, so nothing further to do
        next_fork = sp.second;
        fork_counter += 1;
      } else {
        next_fork = &state;
      }

      // in the false case, allocate new memory for the ptr and
      // constrain the ptr to point to it.
      if (next_fork != nullptr) {

        // pointer may not be null
        if (LazyAllocExisting > 0) {

          unsigned counter = 0;

          // consider any existing objects in memory of the same type
          std::vector<ObjectPair> listOPs;
          next_fork->addressSpace.getMemoryObjects(listOPs, base_type);
          for (const auto &pr : listOPs) {

            if (next_fork == nullptr || counter >= LazyAllocExisting)
              break;

            const MemoryObject *existingMO = pr.first;
            if (existingMO->isLazy()) {

              // fork a new state
              ref<ConstantExpr> ptr = existingMO->getBaseExpr();
              ref<Expr> eq = EqExpr::create(addr, ptr);
              StatePair sp = fork(*next_fork, eq, true);
              counter += 1;
              fork_counter += 1;
              next_fork = sp.second;
            }
          }
        }
        if (next_fork != nullptr) {

          // calc lazyAllocationCount by type i8* (string, byte buffer) gets more
          unsigned count = LazyAllocCount;
          if (base_type->isIntegerTy(8) && count < lazyStringLength + 1) {
            count = lazyStringLength + 1;
          }

          // finally, try with a new object
          WObjectPair wop;
          if (allocSymbolic(*next_fork, base_type, target->inst, MemKind::lazy, '*' + name, wop, 0, count)) {
            ref<ConstantExpr> ptr = wop.first->getOffsetIntoExpr(LazyAllocOffset * (wop.first->created_size / count));
            ref<Expr> eq = EqExpr::create(addr, ptr);
            if (addConstraintOrTerminate(*next_fork, eq)) {
              // insure strings are null-terminated
              fork_counter += 1;
              if (base_type->isIntegerTy(8)) {
                ref<Expr> read = wop.second->read8(count - 1);
                addConstraint(*next_fork, EqExpr::create(read, ConstantExpr::create(0, read->getWidth())));
              }
            } else {
              // state was terminated
            }
          } else {
            terminateStateOnDispose(*next_fork, "lazy symbolic allocation failed");
          }
        }
      }
    }
    if (target && fork_counter > 1) {
      frequent_forkers[target->info->assemblyLine] += (fork_counter - 1);
    }

  } else if (base_type->isFunctionTy()) {

    // unconstrained fn ptrs will expand when invoked
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
    // could not find an object, but op.first points to object before
    terminateStateOnMemFault(state, target, address, op.first, "write resolveMO");
    return false;
  }

  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  if (mo->isReadOnly()) {
    terminateStateOnMemFault(state, target, address, mo, "memory error: object read only");
    return false;
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

      terminateStateOnMemFault(*currState, target, address, mo, "write OoB const offset");
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
      terminateStateOnMemFault(*currState, target, address, mo, "write OoB1 offset");
      if (sp.second != nullptr && sp.second != currState) {
        terminateStateOnMemFault(*sp.second, target, address, mo, "write OoB2 offset");
      }
      return false;

    } else {
      // inbound solution exists.  should continue as currState. sp.second must terminate
      currState = sp.first;
      if (sp.second != nullptr) {
        terminateStateOnMemFault(*sp.second, target, address, mo, "write OoB3 offset");
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
      terminateStateOnMemFault(*currState, target, address, mo, "write memory solver unable to get example offset");
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

MemoryObject *LocalExecutor::allocMemory(Type *type,
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

  if ((kind == MemKind::lazy) && (size < LazyAllocMinSize)) {
    size = LazyAllocMinSize;
  }

  Type *alloc_type = type;
  if (count > 1) {
    alloc_type = ArrayType::get(type, count);
  }

  MemoryObject *mo = memory->allocate(size, alloc_type, kind, allocSite, align);
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
  Type *type = kmodule->module_types.getEquivalentType(type_desc);
  size_t align;
  if (type != nullptr) {
    align = kmodule->targetData->getPrefTypeAlignment(type);
  } else {
    // no matching data type in this module.  treat it as a byte array
    LLVMContext &ctx = kmodule->module->getContext();
    align = kmodule->targetData->getPrefTypeAlignment(Type::getInt32Ty(ctx));
    type = ArrayType::get(Type::getInt8Ty(ctx), size);
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

  // empty symbolic name is rather pointless
  assert(!name.empty());
  wop.first = nullptr;
  wop.second = nullptr;

  MemoryObject *mo = allocMemory(type, allocSite, kind, name, align, count);
  if (mo != nullptr) {
    ObjectState *os = makeSymbolic(state, mo);
    if (os != nullptr) {
      wop.first = mo;
      wop.second = os;
      return true;
    }
    delete mo;
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

void LocalExecutor::unconstrainGlobalVariables(ExecutionState &state, Function *fn) {

  string fn_name = fn->getName();
  for (auto itr = kmodule->module->global_begin(), end = kmodule->module->global_end(); itr != end; ++itr) {
    GlobalVariable *v = itr;

    if (!v->isConstant() && !v->hasHiddenVisibility() && kmodule->isUserGlobal(v) && !kmodule->isDiffGlobalModified(v)) {

      assert(v->hasName());
      string gv_name = v->getName().str();
      auto pos = gv_name.find('.');
      // if dot in first position or the prefix does not equal the function name, continue to next variable
      // if gv name begins with foo.bar then bar is a static local variable to the function foo.
      if (pos == 0) continue;
      if (pos != string::npos && (fn_name != gv_name.substr(0, pos))) continue;

      MemoryObject *mo = globalObjects.find(v)->second;
      if (mo != nullptr) {

        if (mo->size > maxSymbolicSize) {
          if (interpreterOpts.verbose) outs() << "too large unconstrain: " << gv_name << ": " << mo->size << '\n';
        } else {
          if (interpreterOpts.verbose) outs() << "unconstraining: " << gv_name << '\n';

          // replace existing concrete value with symbolic one.
          makeSymbolic(state, mo);
        }
      }
    }
  }
}

void LocalExecutor::unconstrainGlobalValues(ExecutionState &state, Function *fn, unsigned counter) {

  string fn_name = fn->getName();
  for (auto itr = kmodule->module->global_begin(), end = kmodule->module->global_end(); itr != end; ++itr) {
    GlobalVariable *v = itr;
    if (!v->isConstant() && !v->hasHiddenVisibility() && kmodule->isUserGlobal(v) && !kmodule->isDiffGlobalModified(v)) {
      assert(v->hasName());
      string gv_name = v->getName().str();

      // any gv with dot in name should be skipped
      if (gv_name.find('.') == string::npos) {
        if (MemoryObject *mo = globalObjects.find(v)->second) {

          if (mo->size <= maxSymbolicSize) {
            const ObjectState *os = state.addressSpace.findObject(mo);
            ObjectState *wos = state.addressSpace.getWriteable(mo, os);

            WObjectPair wop;
            duplicateSymbolic(state, mo, v, toSymbolName(fn_name, counter, gv_name), wop);
            for (unsigned idx = 0, edx = mo->size; idx < edx; ++idx) {
              wos->write(idx, wop.second->read8(idx));
            }
          }
        }
      }
    }
  }
}

void LocalExecutor::parseBreakAt() {

  // parse out the break-at lines
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
}

void LocalExecutor::bindModule(KModule *kmodule) {

  assert(baseState == nullptr);
  Executor::bindModule(kmodule);

  specialFunctionHandler->setLocalExecutor(this);
  sysModel = new SystemModel(this, optsModel);

  // prepare a generic initial state
  baseState = new ExecutionState();
  baseState->lazyAllocationCount = lazyAllocationCount;
  baseState->lazyStringLength = lazyStringLength;
  baseState->maxLazyDepth = maxLazyDepth;
  baseState->maxStatesInLoop = maxStatesInLoop;

  initializeGlobals(*baseState);
  bindModuleConstants();
  parseBreakAt();

  loadFnPtrMap(interpreterOpts.test_case);

  // look for a libc initializer, execute if found to initialize the base state
  baseState = runFnLibCInit(baseState);
  interpreterHandler->onStateInitialize(*baseState);
}

void LocalExecutor::bindModule(KModule *kmodule, ExecutionState *state, uint64_t mem_reserve) {

  assert(baseState == nullptr);

  memory->reserve(mem_reserve);
  Executor::bindModule(kmodule);

  specialFunctionHandler->setLocalExecutor(this);
  sysModel = new SystemModel(this, optsModel);
  baseState = state;

  reinitializeGlobals(*baseState);
  bindModuleConstants();
  parseBreakAt();

  loadFnPtrMap(interpreterOpts.test_case);
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

void LocalExecutor::loadFnPtrMap(const TestCase *test) {

  if (test != nullptr) {
    for (auto &itr : test->bound_fn_ptrs) {
      uint64_t value = itr.first;
      string fn_name = itr.second;
      if (Function *fn = kmodule->getFunction(fn_name)) {
        replay_fn_ptrs.insert(make_pair(value, fn));
      }
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
  if (!allocSymbolic(*baseState, char_type, fn, MemKind::external, "#stdin_buff", wopStdIn, char_align, SymStdinSize + 1)) {
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

    // if not main, then force global unconstraint
    if (!is_main) {
      unconstraintFlags.setUnconstrainGlobals();
    }

    // unconstrain global state
    if (unconstraintFlags.isUnconstrainGlobals()) {
      unconstrainGlobalVariables(*state, fn);
    }

    // create parameter values
    // if this is main, special case the argument construction
    if (is_main) {

      // symbolic argc, symbolic argv,
      assert(fn->getArgumentList().size() == 2);

      init_states.clear();
      init_states.resize(SymArgsMax+ 1);

      // push the module name into the state
      std::string md_name = kmodule->getModuleIdentifier();
      // program name requires some post-processing.
      // strip paths and bc extension
      std::string prog_name;
      size_t pos = md_name.rfind('/');
      if (pos != string::npos) {
        prog_name = md_name.substr(pos + 1);
      } else {
        prog_name = md_name;
      }
      if (boost::ends_with(prog_name, ".bc")) {
        prog_name = prog_name.substr(0, prog_name.size() - 3);
      }

      // also need to remove a pre, post, or rply prefix so all programs see same prog name
      if (boost::starts_with(prog_name, "prev-")) {
        prog_name = prog_name.substr(4);
      }
      if (boost::starts_with(prog_name, "post-")) {
        prog_name = prog_name.substr(5);
      }
      if (boost::starts_with(prog_name, "rply-")) {
        prog_name = prog_name.substr(5);
      }

      WObjectPair wopProgName;
      if (!allocSymbolic(*state, char_type, fn, MemKind::param, "#program_name", wopProgName, char_align, prog_name.size() + 1)) {
        klee_error("failed to allocate symbolic argv_array");
      }
      MemoryObject *moProgName = wopProgName.first;
      ObjectState *osProgName = wopProgName.second;

      // get the expression width
      ref<Expr> value = osProgName->read8(0);
      Expr::Width width = value->getWidth();

      // create some common constant expressions used frequently
      const ref<ConstantExpr> null = ConstantExpr::create(0, width);

      for (unsigned idx = 0; idx < prog_name.size(); ++idx) {
        ref<Expr> ch = ConstantExpr::create(prog_name[idx], width);
        value = osProgName->read8(idx);
        addConstraint(*state, EqExpr::create(value, ch));
      }

      // null terminate the string
      value = osProgName->read8(prog_name.size());
      addConstraint(*state, EqExpr::create(value, null));

      // get an array for the argv pointers
      WObjectPair wopArgv_array;
      if (!allocSymbolic(*state, str_type, fn, MemKind::param, "argv_array", wopArgv_array, str_align, SymArgsMax + 2)) {
        klee_error("failed to allocate symbolic argv_array");
      }

      // argv[0] -> binary name
      // argv[1 .. SymArgs - 1] = symbolic value
      // argv[SymArgs] = null

      // despite being symbolic, argv[0] always points to program name
      addConstraint(*state, EqExpr::create(wopArgv_array.second->read(0, ptr_width), moProgName->getBaseExpr()));

      // allocate the command line arg strings for each starting state
      init_states[0] = state;
      for (unsigned index = 1; index <= SymArgsMax; ++index) {

        ExecutionState *prev = init_states[index - 1];
        ExecutionState *curr = init_states[index] = new ExecutionState(*prev);

        WObjectPair wopArgv_body;
        std::string argName = "argv_" + itostr(index);
        if (!allocSymbolic(*curr, char_type, fn, MemKind::param, argName, wopArgv_body, char_align, lazyStringLength + 1)) {
          klee_error("failed to allocate symbolic command line arg");
        }

        // constrain strings to command line strings, i.e.
        // [0]  must _not_ be '\0'
        // [N + 1] must be '\0'
        value = wopArgv_body.second->read8(0);
        addConstraint(*curr, NeExpr::create(value, null));

        value = wopArgv_body.second->read8(lazyStringLength);
        addConstraint(*curr, EqExpr::create(value, null));

        // and constrain pointer in argv array to point to body
        ref<Expr> ptr = wopArgv_array.second->read((ptr_width / 8) * (index), ptr_width);
        addConstraint(*curr, EqExpr::create(ptr, wopArgv_body.first->getBaseExpr()));
      }

      for (unsigned idx1 = 0; idx1 <= SymArgsMax; ++idx1) {
        // for each state constrain argc
        ExecutionState *curr = init_states[idx1];

        // and the remainder of the argv array should be null
        for (unsigned idx2 = idx1; idx2 <= SymArgsMax; ++idx2) {
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
  shutdown();
}

void LocalExecutor::runFunctionAsMain(Function *f, int argc, char **argv, char **envp) {
  UNUSED(f);
  UNUSED(argc);
  UNUSED(argv);
  UNUSED(envp);
  assert(false && "deprecated runFunctionAsMain (see runFunctionUnconstrained)");
}

// Used to replay a persisted test case
void LocalExecutor::runFunctionTestCase(const TestCase &test) {

  assert(interpreterOpts.mode == ExecModeID::rply);

  Function *fn = kmodule->module->getFunction(test.entry_fn);
  if (fn == nullptr) return;
  KFunction *kf = kmodule->functionMap[fn];
  if (kf == nullptr) return;

  // restore original unconstraintflags
  unconstraintFlags = test.unconstraintFlags;

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

      case MemKind::output: {
        // output from a symbolic stub.  index for replay
        MemoryObject *mo = injectMemory(*baseState, (void *) obj.addr, obj.data, obj.type, kind, obj.name, obj.count);
        addReplayValue(obj.name, mo);
        break;
      }

      case MemKind::global: {

        // globals should already be injected, unless it is no longer a global
        auto pr = baseState->addressSpace.findMemoryObjectByName(obj.name, kind);
        if (pr.first == nullptr) {
          injectMemory(*baseState, (void *) obj.addr, obj.data, obj.type, kind, obj.name, obj.count);
        } else if (obj.type == to_string(pr.first->type))  {

          // write the test case value
          const MemoryObject *mo = pr.first;
          const ObjectState *os = pr.second;
          assert(mo->name == obj.name && os->getVisibleSize() == obj.data.size());
          ObjectState *wos = baseState->addressSpace.getWriteable(mo, os);
          for (size_t idx = 0, end = obj.data.size(); idx < end; ++idx) {
            wos->write8(idx, obj.data[idx]);
          }
        } else {
          // RLR TODO: report failure
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

  if (kf->isDiffChanged()) {
    state->min_distance = 0;
  }

  std::vector<ExecutionState*> init_states = { state };
  assert(!interpreterOpts.progression.empty());
  timeout = interpreterOpts.progression.front().timeout;
  runFn(kf, init_states);
  shutdown();
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

  ExecutionState *state = new ExecutionState(*baseState, kf, fn->getName());
  if (statsTracker) statsTracker->framePushed(*state, nullptr);

  if (fn->arg_size() == 2) {

    assert(Context::get().getPointerWidth() == 64 && "64-bit only");

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
      state->arguments.clear();
      state->arguments.push_back(eArgC);
      state->arguments.push_back(eArgV);
      interpreterHandler->processTestCase(*state, TerminateReason::Snapshot);
    } else {
      std::vector<ExecutionState *> init_states = {state};
      runFn(kf, init_states);
    }
  }
  shutdown();
}

void LocalExecutor::runFn(KFunction *kf, std::vector<ExecutionState*> &init_states) {

  assert(!init_states.empty());

  // Delay init till now so that ticks don't accrue during
  // optimization and such.
  initTimers();
  BasicBlock *fn_entry = &kf->function->getEntryBlock();
  bool is_entry_targeted = kmodule->isTargetedBBlock(fn_entry);
  unsigned entry = kf->basicBlockEntry[fn_entry];

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

    state->pc = &kf->instructions[entry];
    if (is_entry_targeted) {
      state->reached_target = true;
    }
    addedStates.push_back(state);
  }

  unsigned num_timeouts = 1;
  if (interpreterOpts.mode == ExecModeID::igen) {
    searcher = constructUserSearcher(*this);
  } else {
    searcher = new DFSSearcher();
  }

  updateStates(nullptr);

  MonotonicTimer timer;
  const unsigned tid_timeout = 1;
  const unsigned tid_heartbeat = 2;

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
  unsigned timeout_counter = 0;
  timer.set(tid_heartbeat, HEARTBEAT_INTERVAL);

  HaltReason halt = HaltReason::OK;
  enable_state_switching = true;

  unsigned mem_chk_freq_counter = 0;

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
      if (!state->trace.empty() && break_lines.contains(state->trace.back().second)) {
        outs() << "break at " << state->trace.back().second << '\n';
#ifdef _DEBUG
        enable_state_switching = false;
#endif
      }

      executeInstruction(*state, ki);

    } catch (bad_expression &e) {
      terminateStateOnDispose(*state, "uninitialized expression");
    } catch (solver_failure &e) {
      terminateStateOnDispose(*state, "solver failure");
    }
    processTimers(state, 0);
    updateStates(state);

    assert(addedStates.empty() && removedStates.empty());

    // check for expired timers
    unsigned expired = timer.expired();
    if (expired == tid_timeout) {
      timeout_counter += 1;
      if (timeout_counter == num_timeouts) {
#ifdef _DEBUG
        if (enable_state_switching) halt = HaltReason::TimeOut;
#else
        halt = HaltReason::TimeOut;
#endif
      } else {
        // RLR TODO: this did not work as expected, disabling for now
        inhibitForking = true;
        timer.set(tid_timeout, 60);
        outs() << "Timeout reached, concretizing remaining states" << oendl;
        assert(false);
      }
    } else if (expired == tid_heartbeat) {
      interpreterHandler->resetWatchDogTimer();
      timer.set(tid_heartbeat, HEARTBEAT_INTERVAL);
    }
    if (mem_chk_freq_counter++ % 0xfff) checkMemoryUsage();
  }

  if (!states.empty()) {
    if (!doConcreteInterpretation) {
      klee_message("terminating %lu incomplete states", states.size());
      for (ExecutionState *s : states) {
        terminateStateOnDiscard(*s, "flushing states on halt");
      }
    } else {
      assert(states.size() == 1);
      for (ExecutionState *s : states) {
        terminateStateOnDispose(*s, "timed out on concrete replay");
      }
    }
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
  for (auto s : init_states) {
    delete s;
  }
  init_states.clear();
}

ExecutionState *LocalExecutor::runFnLibCInit(ExecutionState *_state) {

  assert(_state != nullptr);

  ExecutionState *result = nullptr;

  //  Function *libc_init = kmodule->module->getFunction("__uClibc_init");
  if (KFunction *kf_init = kmodule->getKFunction("__uClibc_init")) {

    ExecutionState *init_state = new ExecutionState(*_state, kf_init, kf_init->getName());
    if (statsTracker)
      statsTracker->framePushed(*init_state, nullptr);

    unsigned entry = kf_init->basicBlockEntry[&kf_init->function->getEntryBlock()];
    init_state->pc = &kf_init->instructions[entry];
    processTree = new PTree(init_state);
    init_state->ptreeNode = processTree->root;

    addedStates.push_back(init_state);

    searcher = new DFSSearcher();
    updateStates(nullptr);
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

    // libc initializer should not have forked any additional states
    if (states.empty()) {
      klee_warning("libc initialization failed to yield a valid state");
    } else {
      if (states.size() > 1) {
        klee_warning("libc initialization spawned multiple states");
      }
      result = *states.begin();
      result->popFrame();
      result->addressSpace.clearWritten();
      result->last_ret_value = nullptr;
      states.clear();
    }
    updateStates(nullptr);

    // cleanup
    delete searcher;
    searcher = nullptr;

    delete processTree;
    processTree = nullptr;

    // loop state is no longer valid
    loopingStates.clear();
    if (init_state != result) {
      delete init_state;
    }
  }
  if (_state != result) {
    delete _state;
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

    assert(src_loop == nullptr || isInLoop(&state, kf, src_loop));

    if (src_loop == dst_loop) {
      // either source and destination are not in a loop,
      // or they are in the same loop
      if (dst_loop != nullptr) {

        // both in a loop, if the dest is the loop header, then we have completed a cycle
        if ((dst_loop->getHeader() == dst) && !sf.loopFrames.empty()) {
          LoopFrame &lf = sf.loopFrames.back();
          if (lf.loop == dst_loop) lf.counter += 1;
        }
        assert(isOnlyInLoop(&state, kf, dst_loop));
      }
    } else {

      unsigned src_depth = kf->kloop.getLoopDepth(src);
      unsigned dst_depth = kf->kloop.getLoopDepth(dst);

      // source and destination loop are different
      // we either entered a new loop, or exited the previous loop (or both?)
      if (src_loop == nullptr) {

        // entered the first loop
        assert(sf.loopFrames.empty());
        assert(src_depth == 0 && dst_depth == 1);
        sf.loopFrames.emplace_back(LoopFrame(dst_loop));

        // insert this state into the destination loop set
        // should not be in any loop
        assert(isOnlyInLoop(&state, kf, nullptr));
        loopingStates[dst_loop].insert(&state);

      } else if (dst_loop == nullptr) {

        // left the last loop
        assert(src_depth > 0 && dst_depth == 0);
        for (unsigned idx = 0; idx < src_depth; ++idx) {
          sf.loopFrames.pop_back();
        }
        assert(sf.loopFrames.empty());
        assert(isOnlyInLoop(&state, kf, src_loop));
        // remove this state from the source loop set
        loopingStates[src_loop].erase(&state);

      } else {

        // neither empty implies we just transitioned up/down nested loops
        if (src_depth < dst_depth) {

          assert(src_loop->contains(dst_loop));
          // create frames for each intermediate loop
          const llvm::Loop *curr = dst_loop;
          std::vector<const llvm::Loop*> loops;
          while (curr != src_loop) {
            loops.push_back(curr);
            curr = curr->getParentLoop();
          }
          for (auto itr = loops.rbegin(), end = loops.rend(); itr != end; ++itr) {
            sf.loopFrames.emplace_back(LoopFrame(*itr));
          }
        } else {

          // pop loops from frame until we get to the source
          assert(dst_loop->contains(src_loop));
          for (unsigned idx = 0, end = src_depth - dst_depth; idx < end; ++idx) {
            sf.loopFrames.pop_back();
          }
          assert(sf.loopFrames.back().loop == dst_loop);
        }
        assert(isOnlyInLoop(&state, kf, src_loop));
        loopingStates[src_loop].erase(&state);
        loopingStates[dst_loop].insert(&state);
      }
    }
  }
  if (kmodule->isTargetedBBlock(dst)) {
    state.reached_target = true;
  }
  Executor::transferToBasicBlock(state, src, dst);
}

void LocalExecutor::executeInstruction(ExecutionState &state, KInstruction *ki) {

  if (auto *instr_counters = interpreterOpts.fn_instr_counters) {
    if (!state.stack.empty()) {
      (*instr_counters)[state.stack.back().kf->function] += 1;
    }
  }

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

        const Loop *loop = state.getTopMostLoop();

        ref<Expr> cond = eval(ki, 0, state).value;
        Executor::StatePair branches = fork(state, cond, false);

        // NOTE: There is a hidden dependency here, markBranchVisited
        // requires that we still be in the context of the branch
        // instruction (it reuses its statistic id). Should be cleaned
        // up with convenient instruction specific data.
        if (statsTracker && kf->trackCoverage)
          statsTracker->markBranchVisited(branches.first, branches.second);

        if (branches.first && !branches.second) {
          transferToBasicBlock(*branches.first, src, bi->getSuccessor(0));
        } else if (!branches.first && branches.second) {
          transferToBasicBlock(*branches.second, src, bi->getSuccessor(1));
        } else if (branches.first && branches.second) {

          ExecutionState *states[2] = { branches.first, branches.second };
          BasicBlock *dsts[2] = { bi->getSuccessor(0), bi->getSuccessor(1) };
          bool exceeded_loop = false;
          if (loop != nullptr) {
            auto &ls = loopingStates[loop];
            exceeded_loop = ls.size() > maxStatesInLoop;
          }
          if (inhibitForking || exceeded_loop) {
            // exceeded max num of states in this loop
            // there can be only one...
            unsigned discard = 0;
            if (loop->isLoopExiting(src)) {
              if (!loop->contains(dsts[0])) {
                discard = 1;
              }
            } else if (theRNG.getBool()){
              // discard 1
              discard = 1;
            }
            terminateStateOnDiscard(*states[discard], "loop throttled");
            states[discard] = nullptr;
          } else if (ki) {
            frequent_forkers[ki->info->assemblyLine] += 1;
          }

          if (states[0]) transferToBasicBlock(*states[0], src, dsts[0]);
          if (states[1]) transferToBasicBlock(*states[1], src, dsts[1]);
        }
      }
      break;
    }

    case Instruction::Ret: {

      if (libc_initializing && (state.stack.empty() || !state.stack.back().caller)) {
        libc_initializing = false;
      } else {
        assert(!state.stack.empty());
        KFunction *ret_from = state.stack.back().kf;
        if (!libc_initializing) {
          if (tracer != nullptr) {
            tracer->append_return(state.trace, ret_from);
          }
        }

        if (state.stack.size() > 0 && ret_from->function->hasFnAttribute(Attribute::NoReturn)) {
          // this state completed.  if this was an exit or an abort, we would have
          // handled it at the call site.  Since we don't know what this was, treat it like an abort
          state.last_ret_value = nullptr;
          ostringstream ss;
          ss << "noreturn fn: " << ret_from->getName();
          terminateStateOnComplete(state, TerminateReason::Abort, ss.str());
        } else {
          // if exiting from middle of loop, then
          // need to adjust loop states
          if (!state.stack.empty()) {
            StackFrame &sf = state.stack.back();
            if (!sf.loopFrames.empty()) {
              LoopFrame &lf = sf.loopFrames.back();
              assert(isOnlyInLoop(&state, sf.kf, lf.loop));
              loopingStates[lf.loop].erase(&state);
            }
          }
          Executor::executeInstruction(state, ki);
        }
      }
      break;
    }

    case Instruction::Invoke:
    case Instruction::Call: {

      const CallSite cs(i);
      Value *fp = cs.getCalledValue();

      if (isa<InlineAsm>(fp)) {
        terminateStateOnComplete(state, TerminateReason::UnhandledInst, "inline assembly is unsupported");
        return;
      }

      Function *fn = getTargetFunction(fp, state);

      if (fn == nullptr) {
        // function pointer
        // if concrete or (symbolic and unique), lookup function
        ref<Expr> addr = eval(ki, 0, state).value;
        addr = toUnique(state, addr);
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(addr)) {
          Function *ptr = (Function *) CE->getZExtValue();
          if (kmodule->isDefinedFunction(ptr)) {
            fn = ptr;
          } else if (doConcreteInterpretation) {

            // if not in this function, then could be from unconstrained ptr
            const auto &fnd = replay_fn_ptrs.find(CE->getZExtValue());
            if (fnd != replay_fn_ptrs.end()) {
              fn = (Function*) fnd->second;
            }
          }

        } else {
          if (auto fn_type = dyn_cast<FunctionType>(cast<PointerType>(cs.getCalledValue()->getType())->getElementType())) {
            // else fork states with unique values and restart instruction
            vector<const Function *> matching_fns;
            kmodule->getUserFnsOfType(fn_type, matching_fns);

            const Function *first_match = nullptr;
            for (auto match : matching_fns) {
              ref<Expr> eq = EqExpr::create(addr, Expr::createPointer((uint64_t) match));
              if (solver->mayBeTrue(state, eq)) {

                // save the first for constraint of state
                // others get a state clone
                if (first_match == nullptr) {
                  first_match = match;
                } else {
                  ExecutionState *new_state = clone(&state);
                  addConstraint(*new_state, eq);
                  new_state->bound_fnptrs.insert(make_pair(match, match->getName().str()));
                  new_state->restartInstruction();
                }
              }
            }

            // make sure we found at least one candidate
            if (first_match == nullptr) {
              stringstream ss;
              ss << "no matching function type for function pointer: " << ki->info->assemblyLine;
              terminateStateOnComplete(state, TerminateReason::InvalidCall, ss.str());
            } else {

              // finally, bind the incoming state to the first value
              ref<Expr> eq = EqExpr::create(addr, Expr::createPointer((uint64_t) first_match));
              addConstraint(state, eq);
              state.bound_fnptrs.insert(make_pair(first_match, first_match->getName().str()));
              state.restartInstruction();
            }
            return;
          }
        }
      }

      // if fn is still null, then we have no callee
      if (fn == nullptr) {
        stringstream ss;
        ss << "undefined callee at line: " << ki->info->assemblyLine;
        terminateStateOnComplete(state, TerminateReason::ExternFn, ss.str());
        return;
      }

      string fn_name = fn->getName();

      // check for debugging break
      if (break_fns.contains(fn)) {
        outs() << "break at " << fn_name << '\n';
#ifdef _DEBUG
        enable_state_switching = false;
#endif
      }

      interpreterHandler->incCallCounter(fn);

      // check for a snapshot
      if (interpreterOpts.mode == ExecModeID::irec && interpreterOpts.userSnapshot == fn) {
        state.instFaulting = ki;
        unsigned numArgs = cs.arg_size();

        // evaluate arguments
        state.arguments.reserve(numArgs);
        for (unsigned idx = 0; idx < numArgs; ++idx) {
          ref<Expr> e = eval(ki, idx + 1, state).value;
          state.arguments.push_back(toUnique(state, e));
        }

        interpreterHandler->processTestCase(state, TerminateReason::Snapshot);
        terminateStateOnComplete(state, TerminateReason::Snapshot);
        return;
      }

      // invoke external model of functions
      // these can override defined functions
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

      // if a KFunction is associated with fn, then this call is to a defined function
      KFunction *kf = kmodule->getKFunction(fn);

      // update stats and trace
      if (!libc_initializing) {
        if (kf != nullptr) {
          if (kf->isDiffChanged()) {
            state.linear_distance = 0;
            if (!state.stack.empty() && (state.min_distance > state.stack.size())) {
              state.min_distance = state.stack.size();
            }
          } else if (kf->isUser()) {
            state.linear_distance += 1;
          }

          if (tracer != nullptr) {
            tracer->append_call(state.trace, kf);
          }
        } else {
          state.linear_distance += 1;
        }
      }

      bool should_stub = (kf == nullptr && unconstraintFlags.isUnconstrainExterns()) || unconstraintFlags.isStubCallees();
      bool is_internal = kmodule->isInternalFunction(fn);
      if (libc_initializing || is_internal || !should_stub) {

        // if kf is null here and not an internal fn, we're not in kansas anymore...
        if (kf == nullptr && !is_internal) {
          stringstream ss;
          ss << "external callee: " << fn_name;
          terminateStateOnComplete(state, TerminateReason::ExternFn, ss.str());
          return;
        }

        // make the call
        // evaluate arguments
        unsigned num_args = cs.arg_size();
        std::vector<ref<Expr>> arguments;
        arguments.reserve(num_args);

        for (unsigned idx = 0; idx < num_args; ++idx) {
          arguments.push_back(eval(ki, idx + 1, state).value);
        }

        const FunctionType *fn_type = dyn_cast<FunctionType>(cast<PointerType>(fn->getType())->getElementType());
        const FunctionType *fp_type = dyn_cast<FunctionType>(cast<PointerType>(fp->getType())->getElementType());

        // special case the call with a bitcast case
        if (fn_type && fp_type && fn_type != fp_type) {

          // correct for bitcasts
          unsigned idx = 0;
          for (auto itr = arguments.begin(), end = arguments.end(); itr != end; ++itr) {
            Expr::Width w_fp = (*itr)->getWidth();
            if (idx < fn_type->getNumParams()) {
              Expr::Width w_fn = getWidthForLLVMType(fn_type->getParamType(idx));
              if (w_fp != w_fn) {
                bool isSExt = cs.paramHasAttr(idx + 1, llvm::Attribute::SExt);
                arguments[idx] = isSExt ? SExtExpr::create(arguments[idx], w_fn) : ZExtExpr::create(arguments[idx], w_fn);
              }
            }
            ++idx;
          }
        }
        executeCall(state, ki, fn, arguments);
      } else if (fn->hasFnAttribute(Attribute::NoReturn)) {
        // no need to stub a noreturn fn.
        terminateStateOnComplete(state, TerminateReason::Exit);
        return;
      } else {
        unsigned counter = state.callTargetCounter[fn]++;
        ref<Expr> ret_value;

        if (doConcreteInterpretation) {

          // inject the replay values
          // if kf is null, then this is an external.  do not unconstrain globals
          if (kf != nullptr) {
            replayGlobalValues(state, fn, counter);
          }

          unsigned num_args = cs.arg_size();

          // record specifics of this external call
          state.extern_call_log.emplace_back();
          auto &call = state.extern_call_log.back();
          call.first = fn;
          call.second.reserve(num_args);
          for (unsigned idx = 0; idx < num_args; ++idx) {
            ref<Expr> e = eval(ki, idx + 1, state).value;
            call.second.push_back(toUnique(state, e));
          }

          replayFnCall(state, ki, fn, counter, ret_value);

        } else {
          // use an unconstraining stub
          // if kf is null, then this is an external.  do not unconstrain globals
          if (kf != nullptr) {
            unconstrainGlobalValues(state, fn, counter);
          }
          unconstrainFnCall(state, ki, fn, counter, ret_value);
        }
        if (!ret_value.isNull()) bindLocal(ki, state, ret_value);
      }

      break;
    }

    // Memory instructions...

    case Instruction::Alloca: {

      AllocaInst *ai = cast<AllocaInst>(i);
      unsigned size = (unsigned) kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
      if (ai->isArrayAllocation()) {
        ref<Expr> count = eval(ki, 0, state).value;
        executeAlloca(state, size, count, ai->getAllocatedType(), ki);
      } else {
        executeAlloca(state, size, 1, ai->getAllocatedType(), ki);
      }
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

void LocalExecutor::unconstrainFnCall(ExecutionState &state, KInstruction *ki, llvm::Function *fn, unsigned counter,
                                      ref<Expr> &ret_value) {

  // first get the return value
  CallSite cs(ki->inst);
  string fn_name = fn->getName().str();
  Type *ret_type = cs.getType();
  if (!ret_type->isVoidTy()) {

    WObjectPair wop;
    allocSymbolic(state, ret_type, fn, MemKind::output, toSymbolName(fn_name, counter, 0), wop);
    Expr::Width width = kmodule->targetData->getTypeStoreSizeInBits(ret_type);
    ret_value = wop.second->read(0, width);
  }

  // then consider possible output parameters
  if (fn->isVarArg()) return;

  unsigned idx = 0;
  unsigned edx = cs.arg_size();
  for (auto itr = fn->arg_begin(), end = fn->arg_end(); itr != end && idx < edx; ++itr, ++idx) {
    Argument *arg = itr;
    if (arg->getType()->isPointerTy() && (!kmodule->isConstFnArg(fn, idx))) {
      const Value *v = cs.getArgument(idx);
      if (auto pt = dyn_cast<PointerType>(v->getType())) {
        // some external types may be opaque. have to skip
        Type *type = pt->getPointerElementType();
        if (type->isSized()) {
          ref<Expr> ptr = eval(ki, idx + 1, state).value;
          unconstrainFnArg(state, ki, type, ptr, toSymbolName(fn_name, counter, idx + 1));
        }
      }
    }
  }
}

void LocalExecutor::unconstrainFnArg(ExecutionState &state, KInstruction *ki, Type *type, ref<Expr> &ptr, const string &name) {


  if (interpreterOpts.verbose) {
    outs() << "unconstraining: " << name << oendl;
  }

  // find the referenced memory object
  ObjectPair op;
  if (resolveMO(state, ptr, op) == ResolveResult::OK) {
    const MemoryObject *mo = op.first;

    if (mo->isReadOnly()) {
      outs() << "RLR: what to do with readonly output param\n";
    }

    const ObjectState *os = op.second;
    ref<Expr> bc = os->getBoundsCheckPointer(ptr);
    if (solver->mayBeTrue(state, bc)) {
      if (!solver->mustBeTrue(state, bc)) {
        addConstraint(state, bc);
      }

      // since we'll be writing to this ptr, need to concretize the written address
      ref<ConstantExpr> addr = toConstant(state, ptr, "unconstrainFnArg");
      uint64_t offset = addr->getZExtValue() - mo->address;
      uint64_t size = kmodule->targetData->getTypeStoreSize(type);
      uint64_t count = (os->visible_size - offset) / size;

      // get a writable copy of memory object state
      if (ObjectState *wos = state.addressSpace.getWriteable(mo, os)) {

        // allocate a new symbolic
        WObjectPair wop;
        allocSymbolic(state, type, ki->inst, MemKind::output, name, wop, 0, count);
        for (unsigned idx = 0, end = count * size; idx < end; ++idx) {
          wos->write8(offset + idx, wop.second->read8(idx));
        }
      }
    }
  }
}

void LocalExecutor::replayFnCall(ExecutionState &state, KInstruction *ki, llvm::Function *fn, unsigned counter,
                                 ref<Expr> &ret_value) {

  CallSite cs(ki->inst);
  ReplayFnRec &replay_rec = replay_stub_data[fn][counter];

  Type *ret_type = cs.getType();
  if (!ret_type->isVoidTy()) {

    // lookup and read the return value
    if (const MemoryObject *mo = replay_rec.ret_value) {
      const ObjectState *os = state.addressSpace.findObject(mo);
      Expr::Width w_data = os->visible_size * 8;
      ret_value = os->read(0, w_data);

      // adjust for bit-casts
      Expr::Width w_type = kmodule->targetData->getTypeStoreSizeInBits(ret_type);
      if (w_data != w_type) {
        bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
        ret_value = isSExt ? SExtExpr::create(ret_value, w_type) : ZExtExpr::create(ret_value, w_type);
      }
    } else {
      Expr::Width w_type = kmodule->targetData->getTypeStoreSizeInBits(ret_type);
      ret_value = ConstantExpr::create(0, w_type);
    }
    assert(!ret_value.isNull());
  }

  if (fn->isVarArg()) return;

  unsigned idx = 0;
  unsigned edx = cs.arg_size();
  for (auto itr = fn->arg_begin(), end = fn->arg_end(); itr != end && idx < edx; ++itr, ++idx) {
    Argument *arg = itr;
    if (arg->getType()->isPointerTy() && (!kmodule->isConstFnArg(fn, idx))) {
      const Value *v = cs.getArgument(idx);
      if (v->getType()->isPointerTy()) {

        // both arguments are pointer types and non-constant
        // check for a replay record
        auto lookup = replay_rec.param_values.find(idx);
        if (lookup != replay_rec.param_values.end()) {
          const MemoryObject *mo = lookup->second;

          // found a replay value.  get the actual pointer value
          ref<ConstantExpr> ptr = dyn_cast<ConstantExpr>(eval(ki, idx + 1, state).value);
          if (!ptr.isNull()) {
            replayFnArg(state, mo, ptr);
          }
        }
      }
    }
  }
}

void LocalExecutor::replayFnArg(ExecutionState &state, const MemoryObject *src_mo, const ref<ConstantExpr> &ptr) {

  if (const ObjectState *src_os = state.addressSpace.findObject(src_mo)) {

    // find the referenced memory object
    ObjectPair op;
    if (resolveMO(state, ptr, op) == ResolveResult::OK) {
      const MemoryObject *mo = op.first;

      if (mo->isReadOnly()) {
        outs() << "RLR: what to do with readonly output param\n";
      }

      // get a writable copy of memory object state
      if (ObjectState *wos = state.addressSpace.getWriteable(mo, op.second)) {

        uint64_t offset = ptr->getZExtValue() - mo->address;
        for (unsigned idx = 0, end = src_os->visible_size; idx < end; ++idx) {
          wos->write8(offset + idx, src_os->read8(idx));
        }
      }
    }
  }
}

void LocalExecutor::addReplayValue(const std::string &name, const MemoryObject *mo) {

  vector<string> elements;
  boost::split(elements, name, boost::is_any_of(":"));
  if (elements.size() == 3 && !elements[0].empty() && !elements[1].empty() && !elements[2].empty()) {
    if (Function *fn = kmodule->getFunction(elements[0])) {
      unsigned count = std::stoul(elements[1]);
      ReplayFnRec &replay_rec = replay_stub_data[fn][count];
      if (isdigit(elements[2].front())) {
        unsigned arg_idx = std::stoul(elements[2]);
        if (arg_idx == 0) {
          replay_rec.ret_value = mo;
        } else {
          replay_rec.param_values[arg_idx - 1] = mo;
        }
      } else {
        // RLR TODO: global variables
      }
    }
  }
}

#if 0

// not safe.  getting a symbolic solution more than once can pollute
// the assignment cache
void LocalExecutor::inspectSymbolicSolutions(ExecutionState *state) {

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
#endif

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

bool LocalExecutor::getSymbolicSolution(ExecutionState &state, std::vector<SymbolicSolution> &res, std::vector<ExprSolution> &exprs) {

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


void LocalExecutor::terminateState(ExecutionState &state) {

  if (libc_initializing) {
    errs() << "\ntermination during libc init\n";
    for (const auto &msg : state.messages) {
      errs() << msg << oendl;
    }
  }

  // remove state from any loops
  for (auto itr = state.stack.begin(), end = state.stack.end(); itr != end; ++itr) {
    StackFrame &sf = *itr;
    if (!sf.loopFrames.empty()) {
      LoopFrame &lf = sf.loopFrames.back();
#ifdef _DEBUG
      assert(isOnlyInLoop(&state, sf.kf, lf.loop));
#endif
      loopingStates[lf.loop].erase(&state);
    }
  }
  Executor::terminateState(state);
};

void LocalExecutor::terminateStateOnMemFault(ExecutionState &state,
                                             const KInstruction *ki,
                                             ref<Expr> addr,
                                             const MemoryObject *mo,
                                             const std::string &comment) {
  state.instFaulting = ki;
  state.addrFaulting = toExample(state, addr)->getZExtValue();
  state.moFaulting = mo;
  ostringstream ss;
  ss << comment;
  if (const auto *info = ki->info) {
    ss << " @L" << info->assemblyLine << " ("  << fs::path(info->file).filename().string() << ':' << info->line << "):";
  }
  bool first = true;
  for (const auto &frame : state.stack) {
    if (first) first = false;
    else ss << "->";
    ss << frame.kf->fn_name;
  }
  if (kmodule->isPrevModule()) {
    terminateStateOnDispose(state, ss.str());
  } else {
    terminateStateOnComplete(state, TerminateReason::MemFault, ss.str());
  }
}


bool LocalExecutor::getConcreteSolution(ExecutionState &state,
                                        std::vector<SymbolicSolution> &result,
                                        const std::set_ex<MemKind> &kinds) {

  // need the set of MemoryObjects representing user globals.
  set_ex<const MemoryObject*> global_user_mos;
  set_ex<const llvm::GlobalVariable*> gbs;
  kmodule->getUserGlobals(gbs);
  for (auto &gb : gbs) {
    MemoryObject *mo = globalObjects.find(gb)->second;
    if (mo != nullptr) {
      global_user_mos.insert(mo);
    }
  }

    // copy out all memory objects
  for (auto itr = state.addressSpace.objects.begin(), end = state.addressSpace.objects.end(); itr != end; ++itr) {
    const MemoryObject *mo = itr->first;
    if (kinds.contains(mo->kind)) {

      // only include the user globals
      if (mo->kind != MemKind::global || global_user_mos.contains(mo)) {
        const ObjectState *os = itr->second;
        result.emplace_back(make_pair(mo, vector<unsigned char>{}));
        vector<unsigned char> &value = result.back().second;
        os->readConcrete(value);
      }
    }
  }
  return true;
}

void LocalExecutor::branch(ExecutionState &state, const std::vector< ref<Expr> > &conditions, std::vector<ExecutionState*> &result) {

  set<const Loop*> loops;
  state.getAllLoops(loops);
  Executor::branch(state, conditions, result);
  for (auto &loop : loops) {
    auto &ls = loopingStates[loop];
    for (const auto &ns : result) {
      if (ns != nullptr) ls.insert(ns);
    }
  }
}

ExecutionState *LocalExecutor::clone(ExecutionState *state) {

  set<const Loop*> loops;
  state->getAllLoops(loops);
  ExecutionState *result = Executor::clone(state);
  if (result != nullptr) {
    for (auto &loop : loops) {
      loopingStates[loop].insert(result);
    }
  }
  return result;
}

Executor::StatePair LocalExecutor::fork(ExecutionState &current, ref<Expr> condition, bool isInternal) {

  set<const Loop*> loops;
  current.getAllLoops(loops);
  StatePair pr = Executor::fork(current, condition, isInternal);
  for (auto &loop : loops) {
    auto &ls = loopingStates[loop];
    if (pr.first != nullptr) {
      ls.insert(pr.first);
    }
    if (pr.second != nullptr) {
      ls.insert(pr.second);
    }
  }
  return pr;
}

uint64_t LocalExecutor::getUsedMemory() const {
  return memory == nullptr ? 0 : memory->getUsedDeterministicSize();
}

Interpreter *Interpreter::createLocal(LLVMContext &ctx,
                                      const InterpreterOptions &opts,
                                      InterpreterHandler *ih) {
  return new LocalExecutor(ctx, opts, ih);
}

}


///

