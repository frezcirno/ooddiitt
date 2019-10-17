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
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/FloatEvaluation.h"
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

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#include <fstream>
#include <boost/algorithm/string.hpp>
#include <llvm/IR/Intrinsics.h>
#include <llvm/DebugInfo.h>

#define LEN_CMDLINE_ARGS 8
#define MIN_LAZY_STRING_LEN 9

using namespace llvm;
using namespace std;

namespace klee {

#define countof(a) (sizeof(a)/ sizeof(a[0]))

// RLR TODO: this really needs to go somewhere better
void fromDataString(vector<unsigned char> &data, const string &str) {

  assert(str.size() % 2 == 0);
  data.clear();
  data.reserve(str.size() / 2);

  unsigned char val = 0;
  unsigned counter = 0;
  for (const auto &ch : str) {
    unsigned char nibble = 0;
    if (isdigit(ch)) nibble = ch - '0';
    else if (ch >= 'A' && ch <= 'F') nibble = ch - 'A' + 10;
    if (counter++ % 2 == 0) {
      val = nibble;
    } else {
      val = (val << 4) | nibble;
      data.push_back(val);
    }
  }
}

class bad_expression : public std::runtime_error
{
public:
  bad_expression() : std::runtime_error("null expression") {}
  bad_expression(const char *msg) : std::runtime_error(msg) {}
};

cl::opt<unsigned>
    SymArgs("sym-args",
            cl::init(0),
            cl::desc("Maximum number of command line arguments"));

cl::opt<bool>
  VerifyConstraints("verify-constraints",
                    cl::init(false),
                    cl::desc("Perform additional constraint verification before adding"));

cl::opt<unsigned>
  LazyAllocationCount("lazy-allocation-count",
                       cl::init(1),
                       cl::desc("Number of items to lazy initialize pointer"));

cl::opt<unsigned>
  LazyAllocationOffset("lazy-allocation-offset",
                       cl::init(0),
                       cl::desc("index into lazy allocation to return"));

cl::opt<unsigned>
  MinLazyAllocationSize("lazy-allocation-minsize",
                        cl::init(0),
                        cl::desc("minimum size of a lazy allocation"));

cl::opt<unsigned>
  LazyAllocationDepth("lazy-allocation-depth",
                      cl::init(4),
                      cl::desc("Depth of items to lazy initialize pointer"));

cl::opt<unsigned>
  LazyAllocationExt("lazy-allocation-ext",
                    cl::init(2),
                    cl::desc("number of lazy allocations to include existing memory objects of same type"));

cl::opt<unsigned>
  MaxLoopIteration("max-loop-iteration",
                   cl::init(4),
                   cl::desc("Number of loop iterations"));

cl::opt<unsigned>
  MaxLoopForks("max-loop-forks",
                  cl::init(16),
                  cl::desc("Number of forks within loop body"));


LocalExecutor::LocalExecutor(LLVMContext &ctx, const InterpreterOptions &opts, InterpreterHandler *ih) :
  Executor(ctx, opts, ih),
  lazyAllocationCount(LazyAllocationCount),
  maxLoopIteration(MaxLoopIteration),
  maxLoopForks(MaxLoopForks),
  maxLazyDepth(LazyAllocationDepth),
  maxStatesInLoop(10000),
  baseState(nullptr),
  heap_base(opts.heap_base),
  progression(opts.progression),
  libc_initializing(false) {

  memory->setBaseAddr(heap_base);
  switch (opts.mode) {
    case ExecModeID::igen:
      doSaveFault = false;
      doAssumeInBounds = true;
      doLocalCoverage = false;
      break;
    case ExecModeID::rply:
      break;
    default:
      klee_error("invalid execution mode");
  }

  Executor::setVerifyContraints(VerifyConstraints);
}

LocalExecutor::~LocalExecutor() {

  if (statsTracker) {
    statsTracker->done();
  }

  if (baseState != nullptr) {
    // this last state is leaked.  something in solver
    // tear-down does not like its deletion
//    delete baseState;
    baseState = nullptr;

  }
}

bool LocalExecutor::addConstraintOrTerminate(ExecutionState &state, ref<Expr> e) {

  if (VerifyConstraints) {
    std::vector<SymbolicSolution> in;
    getSymbolicSolution(state, in);
  }

  if (solver->mayBeTrue(state, e)) {
    addConstraint(state, e);

    if (VerifyConstraints) {
      std::vector<SymbolicSolution> out;
      getSymbolicSolution(state, out);
    }

    return true;
  }
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

bool LocalExecutor::isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e) {

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

void LocalExecutor::newUnconstrainedGlobalValues(ExecutionState &state, Function *fn, unsigned counter) {


  // RLR TODO: replace old proginfo
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

  if ((countLoadIndirection(type) > 1) && isUnconstrainedPtr(*currState, e)) {

    // this is an unconstrained ptr-ptr.
    expandLazyAllocation(state, e, false, type->getPointerElementType(), target, mo->name);
  }
  return true;
}

void LocalExecutor::expandLazyAllocation(ExecutionState &state, ref<Expr> addr, bool restart,
                                         const llvm::Type *type, KInstruction *target, const std::string &name) {

  // count current depth of lazy allocations
  unsigned depth = 0;
  for (auto end = (unsigned) name.size(); depth < end && name.at(depth) == '*'; ++depth);

  ref<ConstantExpr> null = Expr::createPointer(0);
  ref<Expr> eqNull = EqExpr::create(addr, null);

  if (depth >= maxLazyDepth) {

    // too deep. no more forking for this pointer.
    addConstraintOrTerminate(state, eqNull);
    if (restart) state.restartInstruction();

  } else {

    StatePair sp = fork(state, eqNull, true);

    // in the true case, ptr is null, so nothing further to do
    if (restart && sp.first != nullptr) sp.first->restartInstruction();

    ExecutionState *next_fork = sp.second;

    // in the false case, allocate new memory for the ptr and
    // constrain the ptr to point to it.
    if (next_fork != nullptr) {

      if (restart) next_fork->restartInstruction();

      // pointer may not be null
      Type *base_type = type->getPointerElementType();
      if (base_type->isFirstClassType()) {

        if (LazyAllocationExt > 0) {

          unsigned counter = 0;

          // consider any existing objects in memory of the same type
          std::vector<ObjectPair> listOPs;
          sp.second->addressSpace.getMemoryObjects(listOPs, base_type);
          for (const auto &pr : listOPs) {

            if (next_fork == nullptr || counter >= LazyAllocationExt) break;

            const MemoryObject *existingMO = pr.first;
            if (existingMO->kind == MemKind::lazy) {

              // fork a new state
              ref<ConstantExpr> ptr = existingMO->getBaseExpr();
              ref<Expr> eq = EqExpr::create(addr, ptr);
              StatePair sp2 = fork(*next_fork, eq, true);
              counter += 1;
              next_fork = sp2.second;
              if (restart && next_fork != nullptr) next_fork->restartInstruction();
            }
          }
        }
        if (next_fork != nullptr) {

          // calc lazyAllocationCount by type i8* (string, byte buffer) gets more
          unsigned count = LazyAllocationCount;
          if (base_type->isIntegerTy(8) && count < MIN_LAZY_STRING_LEN) {
            count = MIN_LAZY_STRING_LEN;
          }

          // finally, try with a new object

          WObjectPair wop;
          allocSymbolic(*next_fork, base_type, target->inst, MemKind::lazy, '*' + name, wop, 0, count);
          ref<ConstantExpr> ptr = wop.first->getOffsetIntoExpr(LazyAllocationOffset * (wop.first->created_size / count));
          ref<Expr> eq = EqExpr::create(addr, ptr);
          addConstraintOrTerminate(*next_fork, eq);

          // insure strings are null-terminated
          if (base_type->isIntegerTy(8)) {
            next_fork->addConstraint(EqExpr::create(wop.second->read8(count - 1), ConstantExpr::create(0, Expr::Int8)));
          }

          if (restart) next_fork->restartInstruction();
        }
      }
    }
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
    if (solver->getValue(*currState, offsetExpr, cex)) {
      ref<Expr> eq = EqExpr::create(offsetExpr, cex);
      if (!solver->mustBeTrue(*currState, eq)) {
        klee_warning("Concretized offset on write");
        if (!addConstraintOrTerminate(*currState, eq)) {
          return false;
        }
      }
      offsetExpr = cex;
    } else {
      terminateStateOnFault(*currState, target, "write memory solver unable to get example offset");
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

  if (mo->created_size > 4096) {
    klee_warning("large symbolic: %s, size=%d", mo->name.c_str(), mo->created_size);
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
                                         llvm::Type *type,
                                         const llvm::Value *allocSite,
                                         MemKind kind,
                                         const std::string &name,
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

  assert(unconstraintFlags.isUnconstrainGlobals());

  std::string fn_name = fn->getName();
  for (auto itr = kmodule->module->global_begin(), end = kmodule->module->global_end(); itr != end; ++itr) {
    const GlobalVariable *v = static_cast<const GlobalVariable *>(itr);
    MemoryObject *mo = globalObjects.find(v)->second;
    std::string gb_name = mo->name;

    // RLR TODO: this need a permanent fix without progInfo
    if ((gb_name.size() > 0) && (gb_name.at(0) != '.') /* && (progInfo->isGlobalInput(fn_name, gb_name)) */ ) {
      // global may already have a value in this state. if so unlink it.
      const ObjectState *os = state.addressSpace.findObject(mo);
      if (os != nullptr) {
        state.addressSpace.unbindObject(mo);
      }
      makeSymbolic(state, mo);
    }
  }
}

const Module *LocalExecutor::setModule(llvm::Module *module, const ModuleOptions &opts) {

  assert(kmodule == nullptr);
  const Module *result = Executor::setModule(module, opts);
// DELETEME:  kmodule->prepareMarkers(opts, interpreterHandler);
  specialFunctionHandler->setLocalExecutor(this);

  void *addr_offset = nullptr;
  if (Context::get().getPointerWidth() == Expr::Int32) {
    addr_offset = heap_base;
  }

  // prepare a generic initial state
  baseState = new ExecutionState(addr_offset);
  baseState->maxLoopIteration = maxLoopIteration;
  baseState->lazyAllocationCount = lazyAllocationCount;
  baseState->maxLazyDepth = maxLazyDepth;
  baseState->maxLoopForks = maxLoopForks;

  initializeGlobals(*baseState, addr_offset);
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

//  pathsFaulting.clear(0);
  faulting_state_stash.clear();
//  auto num_reachable_paths = pathsRemaining.size();

  if (pathWriter) baseState->pathOS = pathWriter->open();
  if (symPathWriter) baseState->symPathOS = symPathWriter->open();

  // look for a libc initializer, execute if found to initialize the base state
  Function *libc_init = kmodule->module->getFunction("__uClibc_init");
  if (libc_init != nullptr) {
    KFunction *kf_init = kmodule->functionMap[libc_init];
    ExecutionState *state = new ExecutionState(*baseState, kf_init, libc_init->getName());
    if (statsTracker) statsTracker->framePushed(*state, nullptr);
    ExecutionState *initState = runLibCInitializer(*state, libc_init);
    if (initState != nullptr) {
      delete baseState;
      baseState = initState;
    }
  }

  std::vector<ExecutionState*> init_states;

  // iterate through each phase of unconstrained progression
  for (auto itr = progression.begin(), end = progression.end(); itr != end; ++itr) {

    const auto &desc = *itr;
    init_states.clear();

    // initialize a common initial state
    ExecutionState *state = new ExecutionState(*baseState, kf, name);
    if (statsTracker) statsTracker->framePushed(*state, nullptr);

    // when substituting unconstraining stubs, remaining paths
    // must be filtered to only entry function
#if 0 == 1
    if (desc.unconstraintFlags.test(UNCONSTRAIN_STUB_FLAG)) {
      pathsRemaining.clear(kf->fnID);
    }

    // done if our objective is local coverage and there are no paths remaining
    if (doLocalCoverage && pathsRemaining.empty()) break;
#endif

    timeout = desc.timeout;
    unconstraintFlags |= desc.unconstraintFlags;

    // unconstrain global state
    if (unconstraintFlags.isUnconstrainGlobals()) {
      unconstrainGlobals(*state, fn);
    }

    // create parameter values
    // if this is main, special case the argument construction
    if (isMainEntry(fn)) {

      init_states.resize(SymArgs + 1, nullptr);

      // symbolic argc, symbolic argv,
      const auto &args = fn->getArgumentList();
      const Argument &argc = args.front();
      const Argument &argv = args.back();

      // argc constrained 1 .. SymArgs + 1
      WObjectPair wopArgc;
      Type *argType = argc.getType();
      allocSymbolic(*state, argType, &argc, MemKind::param, "argc", wopArgc, argc.getParamAlignment());
      ref<Expr> eArgc = wopArgc.second->read(0, kmodule->targetData->getTypeAllocSizeInBits(argType));
      bindArgument(kf, 0, *state, eArgc);

      unsigned ptr_width =  Context::get().getPointerWidth();

      // push the binary name into the state
      std::string md_name = kmodule->module->getModuleIdentifier();
      const MemoryObject *moProgramName = addExternalObject(*state, (void*) md_name.c_str(), md_name.size() + 1, false);

      // get an array for the argv pointers
      WObjectPair wopArgv_array;
      argType = argv.getType()->getPointerElementType();
      allocSymbolic(*state, argType, &argv, MemKind::fixed, "argv_array", wopArgv_array, 0, SymArgs + 2);

      // argv[0] -> binary name
      // argv[1 .. SymArgs] = symbolic value

      // despite being symbolic, argv[0] always points to program name
      state->addConstraint(EqExpr::create(wopArgv_array.second->read(0, ptr_width), moProgramName->getBaseExpr()));

      // and finally, the pointer to the argv array to be passed as param to main
      WObjectPair wopArgv;
      argType = argv.getType();
      allocSymbolic(*state, argType, &argv, MemKind::param, "argv", wopArgv, argv.getParamAlignment(), 1);

      ref<Expr> eArgv = wopArgv.second->read(0, kmodule->targetData->getTypeAllocSizeInBits(argType));
      state->addConstraint(EqExpr::create(wopArgv_array.first->getBaseExpr(), eArgv));
      bindArgument(kf, 1, *state, eArgv);

      // allocate the command line arg strings for each starting state
      init_states[0] = state;
      for (unsigned index = 1; index <= SymArgs; index++) {

        ExecutionState *prev = init_states[index - 1];
        ExecutionState *curr = init_states[index] = new ExecutionState(*prev);

        WObjectPair wopArgv_body;
        std::string argName = "argv_" + itostr(index);
        argType = argv.getType()->getPointerElementType()->getPointerElementType();
        allocSymbolic(*curr, argType, &argv, MemKind::fixed, argName.c_str(), wopArgv_body, 0, LEN_CMDLINE_ARGS + 1);
        // null terminate the string
        curr->addConstraint(EqExpr::create(wopArgv_body.second->read8(LEN_CMDLINE_ARGS), ConstantExpr::create(0, Expr::Int8)));

        // and constrain pointer in argv array to point to body
        ref<Expr> ptr = wopArgv_array.second->read((ptr_width / 8) * (index), ptr_width);
        curr->addConstraint(EqExpr::create(ptr, wopArgv_body.first->getBaseExpr()));
      }

      for (unsigned index = 0; index <= SymArgs; index++) {
        // for each state constrain argc
        ExecutionState *curr = init_states[index];
        curr->addConstraint(EqExpr::create(ConstantExpr::create(index + 1, Expr::Int32), eArgc));

        // and the remainor of the argv array should be null
        for (unsigned idx = index; idx <= SymArgs; idx++) {
          ref<Expr> ptr = wopArgv_array.second->read((ptr_width / 8) * (idx + 1), ptr_width);
          curr->addConstraint(EqExpr::create(ptr, ConstantExpr::createPointer(0)));
        }
      }

    } else {

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
        ref<Expr> e = wop.second->read(0, kmodule->targetData->getTypeAllocSizeInBits(argType));
        bindArgument(kf, index, *state, e);
      }
      init_states.push_back(state);
    }
    runFn(kf, init_states);
  }
  outs() << name << ": generated " << interpreterHandler->getNumTestCases() << " test case(s)\n";
}

void LocalExecutor::runFunctionAsMain(Function *f, int argc, char **argv, char **envp) {

}

void LocalExecutor::runFunctionTestCase(const TestCase &test) {

  Function *fn = kmodule->module->getFunction(test.entry_fn);
  if (fn == nullptr) return;
  KFunction *kf = kmodule->functionMap[fn];
  if (kf == nullptr) return;

  faulting_state_stash.clear();

 // look for a libc initializer, execute if found to initialize the base state
  Function *libc_init = kmodule->module->getFunction("__uClibc_init");
  if (libc_init != nullptr) {
    KFunction *kf_init = kmodule->functionMap[libc_init];
    ExecutionState *state = new ExecutionState(*baseState, kf_init, libc_init->getName());
    if (statsTracker) statsTracker->framePushed(*state, nullptr);
    ExecutionState *initState = runLibCInitializer(*state, libc_init);
    if (initState != nullptr) {
      delete baseState;
      baseState = initState;
    }
  }

  std::vector<ExecutionState*> init_states;
  ExecutionState *state = new ExecutionState(*baseState, kf, test.entry_fn);
  if (statsTracker) statsTracker->framePushed(*state, nullptr);

  std::map<std::string,const TestObject*> to_obj;
  for (const auto &obj : test.objects) {
    to_obj[obj.name] = &obj;
  }

  if (test.entry_fn == "toarith") {

    unsigned index = 0;
    for (Function::const_arg_iterator ai = fn->arg_begin(), ae = fn->arg_end(); ai != ae; ++ai, ++index) {

      const Argument &arg = *ai;
      std::string argName = arg.getName();
      Type *argType = arg.getType();
      size_t argAlign = arg.getParamAlignment();
      vector<unsigned char> data;

      if (argType->isPointerTy()) {
        const TestObject *v = to_obj["v"];
        const TestObject *ptr_v = to_obj["*v"];
        const TestObject *ptr_ptr_v = to_obj["**v"];
        assert(v && ptr_v);

        MemoryObject *mo_ptr_ptr_v = nullptr;
        ObjectState *wo_ptr_ptr_v = nullptr;
        if (ptr_ptr_v != nullptr) {
          Type *char_type = Type::getInt8Ty(kmodule->module->getContext());
          unsigned alignment = kmodule->targetData->getPrefTypeAlignment(char_type);
          mo_ptr_ptr_v = allocMemory(*state, char_type, &arg, MemKind::param, "**v", alignment, ptr_ptr_v->count);
          wo_ptr_ptr_v = bindObjectInState(*state, mo_ptr_ptr_v);
          // write out the string
          fromDataString(data, ptr_ptr_v->data);
          for (unsigned idx = 0, end = data.size(); idx < end; ++idx) {
            wo_ptr_ptr_v->write8(idx, data[idx]);
          }
        }
        Type *ptd_type = argType->getPointerElementType();
        unsigned alignment = kmodule->targetData->getPrefTypeAlignment(ptd_type);
        MemoryObject *mo_ptr_v = allocMemory(*state, ptd_type, &arg, MemKind::param, "*v", alignment, ptr_v->count);
        ObjectState *wo_ptr_v = bindObjectInState(*state, mo_ptr_v);
        fromDataString(data, ptr_v->data);

        // if ptr-ptr is not null, then need to insert the pointer
        unsigned copy_end = data.size();
        if (mo_ptr_ptr_v != nullptr) {
          copy_end = 8;
          ref<ConstantExpr> e_ptr_ptr_v = ConstantExpr::createPointer(mo_ptr_ptr_v->address);
          wo_ptr_v->write(8, e_ptr_ptr_v);
        }

        for (unsigned idx = 0; idx < copy_end; ++idx) {
          wo_ptr_v->write8(idx, data[idx]);
        }

        MemoryObject *mo_v = allocMemory(*state, argType, &arg, MemKind::param, "v", alignment, v->count);
        ObjectState *wo_v = bindObjectInState(*state, mo_v);
        ref<ConstantExpr> e_ptr_v = ConstantExpr::createPointer(mo_ptr_v->address);
        wo_v->write(0, e_ptr_v);

        ref<Expr> e = wo_v->read(0, kmodule->targetData->getTypeAllocSizeInBits(argType));
        bindArgument(kf, index, *state, e);
      }
    }
  } else if (test.entry_fn == "set_fields") {

    const Argument &arg = fn->getArgumentList().front();
    std::string argName = arg.getName();
    Type *argType = arg.getType();
    size_t argAlign = arg.getParamAlignment();

    const TestObject *ptr_str = to_obj["*fieldstr"];
    assert(ptr_str);

    vector<unsigned char> data;

    MemoryObject *mo_ptr_str = nullptr;
    ObjectState *wo_ptr_str = nullptr;
    Type *char_type = Type::getInt8Ty(kmodule->module->getContext());
    unsigned alignment = kmodule->targetData->getPrefTypeAlignment(char_type);
    mo_ptr_str = allocMemory(*state, char_type, &arg, MemKind::param, "*fieldstr", alignment, ptr_str->count);
    wo_ptr_str = bindObjectInState(*state, mo_ptr_str);
    // write out the string
    fromDataString(data, ptr_str->data);
    for (unsigned idx = 0, end = data.size(); idx < end; ++idx) {
      wo_ptr_str->write8(idx, data[idx]);
    }

    MemoryObject *mo_str = allocMemory(*state, argType, &arg, MemKind::param, "fieldstr", alignment, 1);
    ObjectState *wo_str = bindObjectInState(*state, mo_str);
    ref<ConstantExpr> e_ptr_str = ConstantExpr::createPointer(mo_ptr_str->address);
    wo_str->write(0, e_ptr_str);

    ref<Expr> e = wo_str->read(0, kmodule->targetData->getTypeAllocSizeInBits(argType));
    bindArgument(kf, 0, *state, e);
  }

  init_states.push_back(state);
  runFn(kf, init_states);
}

void LocalExecutor::runFn(KFunction *kf, std::vector<ExecutionState*> &init_states) {

  assert(!init_states.empty());
  Function *fn = kf->function;

  llvm::raw_ostream &os = interpreterHandler->getInfoStream();
  os << fn->getName().str() << ": " << interpreterHandler->flags_to_string(unconstraintFlags) << '\n';
  os.flush();

  // Delay init till now so that ticks don't accrue during
  // optimization and such.
  initTimers();

  const BasicBlock *fn_entry = &kf->function->getEntryBlock();
  unsigned entry = kf->basicBlockEntry[const_cast<BasicBlock*>(fn_entry)];
  std::vector<const llvm::Loop*> loops;

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

    StackFrame &sf = state->stack.back();
    for (auto itr = loops.rbegin(), end = loops.rend(); itr != end; ++itr) {
      sf.loopFrames.emplace_back(LoopFrame(*itr));
    }
    state->pc = &kf->instructions[entry];
    addedStates.push_back(state);
  }

  searcher = constructUserSearcher(*this);
  updateStates(nullptr);

  MonotonicTimer timer;
  const unsigned tid_timeout = 1;
  const unsigned tid_heartbeat = 2;

  if (timeout > 0) timer.set(tid_timeout, timeout);
  timer.set(tid_heartbeat, HEARTBEAT_INTERVAL);

  HaltReason halt = HaltReason::OK;

  while (!states.empty() &&
         !haltExecution &&
         halt == HaltReason::OK /* &&
         !(doLocalCoverage && pathsRemaining.empty(kf->fnID)) */) {

    ExecutionState *state = &searcher->selectState();
    KInstruction *ki = state->pc;
    stepInstruction(*state);

    try {
      if (ki->info->assemblyLine == UINT32_MAX) {
        outs() << "break here\n";
      }
      executeInstruction(*state, ki);

      const DebugLoc loc = ki->inst->getDebugLoc();
      unsigned line = loc.getLine();
      if (state->assembly_trace.empty() || line != state->assembly_trace.back()) {
        state->assembly_trace.push_back(line);
      }

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
      halt = HaltReason::TimeOut;
    } else if (expired == tid_heartbeat) {
      interpreterHandler->resetWatchDogTimer();
      timer.set(tid_heartbeat, HEARTBEAT_INTERVAL);
    }
    checkMemoryFnUsage(kf);
  }

  loopForkCounter.clear();
  for (ExecutionState *state : states) {
    terminateState(*state, "flushing states on halt");
  }
  updateStates(nullptr);
  assert(states.empty());

  delete searcher;
  searcher = nullptr;

  delete processTree;
  processTree = nullptr;

  // now consider our stashed faulting states
#if 0 == 1
  for (ExecutionState *state : faulting_state_stash) {
    if (removeCoveredRemainingPaths(*state)) {
      interpreterHandler->processTestCase(*state);
    }
    delete state;
  }
#endif
  faulting_state_stash.clear();
}

ExecutionState *LocalExecutor::runLibCInitializer(klee::ExecutionState &state, llvm::Function *initializer) {

  ExecutionState *result = nullptr;

  KFunction *kf = kmodule->functionMap[initializer];
  unsigned entry = kf->basicBlockEntry[&initializer->getEntryBlock()];
  state.pc = &kf->instructions[entry];

  processTree = new PTree(&state);
  state.ptreeNode = processTree->root;

  states.insert(&state);

  searcher = new DFSSearcher();
  std::vector<ExecutionState *> newStates(states.begin(), states.end());
  searcher->update(nullptr, newStates, std::vector<ExecutionState *>());
  libc_initializing = true;

  while (libc_initializing) {

    ExecutionState *state;
    state = &searcher->selectState();
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
    klee_warning("libc initialization spawned multiple states");
  }
  if (states.empty()) {
    klee_warning("libc initialization failed to yield a valid state");
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

void LocalExecutor::terminateState(ExecutionState &state, const Twine &message) {

  for (auto &sf : state.stack) {
    state.extractITrace(sf);
  }

  if (state.status == ExecutionState::StateStatus::Completed) {
    if (!doLocalCoverage /* || removeCoveredRemainingPaths(state) */) {
      interpreterHandler->processTestCase(state);
    }
  } else {
    // its an error state, pending state, or discarded state
    // stash faults for later consideration
#if 0 == 1
    if (addCoveredFaultingPaths(state)) {
      faulting_state_stash.insert(new ExecutionState(state));
    }
#endif
  }
  Executor::terminateState(state, message);
}

void LocalExecutor::terminateStateOnExit(ExecutionState &state) {
  state.status = ExecutionState::StateStatus::Completed;
  Executor::terminateStateOnExit(state);
}

void LocalExecutor::terminateStateOnFault(ExecutionState &state, const KInstruction *ki, const llvm::Twine &message) {
  state.status = ExecutionState::StateStatus::Faulted;
  state.instFaulting = ki;
  state.terminationMessage = message.str();
  terminateState(state, message);
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

  // expensive, so do not do this very often
  if ((maxStatesInLoop > 0) && (stats::instructions & 0xFFF) == 0) {
    if (kf != nullptr) {

      // get a vector of all loops in fn
      std::deque<const Loop*> worklist;
      for (const Loop *root : kf->loopInfo) {
        worklist.push_back(root);
      }

      // loops may be nested, so do a dfs
      std::vector<const Loop*> all_loops;
      while (!worklist.empty()) {
        const Loop *curr = worklist.front();
        worklist.pop_front();
        all_loops.push_back(curr);
        for (const Loop *child : *curr) {
          worklist.push_back(child);
        }
      }

      for (const Loop *loop : all_loops) {
        unsigned num = numStatesInLoop(loop);
        if (num > maxStatesInLoop) {
          unsigned killed = decimateStatesInLoop(loop, 99);

          // try to get a marker number for this basic block
          unsigned marker = 0;
          Instruction &i = loop->getHeader()->front();

          std::string loop_id;
          raw_string_ostream ss(loop_id);
          loop->getLoopID()->print(ss);
          ss.flush();
          outs() << "terminated " << killed << " states in loop: " << loop_id << "\n";
        }
      }
    }
  }
}

unsigned LocalExecutor::decimateStatesInLoop(const Loop *loop, unsigned skip_counter) {

  unsigned counter = 0;
  unsigned killed = 0;
  skip_counter++;
  for (ExecutionState *state : states) {
    if (!state->stack.empty()) {
      const StackFrame &sf = state->stack.back();
      if (!sf.loopFrames.empty()) {
        const LoopFrame &lf = sf.loopFrames.back();
        if ((lf.loop == loop) && (++counter % skip_counter != 0)) {
          state->status = ExecutionState::StateStatus::Decimated;
          terminateState(*state, "decimated");
          killed++;
        }
      }
    }
  }
  return killed;
}

unsigned LocalExecutor::numStatesInLoop(const Loop *loop) const {

  unsigned counter = 0;
  for (const ExecutionState *state : states) {
    if (!state->stack.empty()) {
      const StackFrame &sf = state->stack.back();
      if (!sf.loopFrames.empty()) {
        const LoopFrame &lf = sf.loopFrames.back();
        if (lf.loop == loop) ++counter;
      }
    }
  }
  return counter;
}

#if 0 == 1

void LocalExecutor::getReachablePaths(const std::string &fn_name, M2MPaths &paths, bool transClosure) const {

  paths.empty();

  // add this functions paths
  unsigned fnID = progInfo->getFnID(fn_name);
  if (fnID != 0) {
    const auto fn_paths = progInfo->get_m2m_paths(fn_name);
    if (fn_paths != nullptr) {
      paths[fnID] = *fn_paths;
    }
  }

  if (transClosure) {
    // and then every path from call graph decendents
    auto reachableFns = progInfo->getReachableFns(fn_name);
    if (reachableFns != nullptr) {
      for (const auto &name : *reachableFns) {
        unsigned id = progInfo->getFnID(name);
        if (id != 0 && id != fnID) {
          const auto fn_paths = progInfo->get_m2m_paths(fn_name);
          if (fn_paths != nullptr) {
            paths[fnID] = *fn_paths;
          }
        }
      }
    }
  }
}

void LocalExecutor::getAllPaths(M2MPaths &paths) const {

  paths.empty();

  // for each function in the transitive closure, insert m2m paths
  for (KFunction *kf: kmodule->functions) {
    Function *fn = kf->function;
    std::string fn_name = fn->getName();
    unsigned fnID = progInfo->getFnID(fn_name);
    if (fnID != 0) {
      const auto fn_paths = progInfo->get_m2m_paths(fn_name);
      if (fn_paths != nullptr) {
        paths[fnID] = *fn_paths;
      }
    }
  }
}

bool LocalExecutor::reachesRemainingPath(const KFunction *kf, const llvm::BasicBlock *bb) const {

  // construct a set of m2m path headers
  std::set<const BasicBlock*> path_headers;

  // iterate through paths remining in this function
  auto itr1 = pathsRemaining.find(kf->fnID);
  if (itr1 != pathsRemaining.end()) {
    for (auto path : itr1->second) {

      // insert head of path into set
      unsigned head = stoi(path.substr(1, path.find('.', 1)));
      auto itr2 = kf->mapBBlocks.find(head);
      if (itr2 != kf->mapBBlocks.end()) {
        path_headers.insert(itr2->second);
      }
    }
  }

  // return reachability from bb to any of the headers
  bool result = false;
  if (!path_headers.empty()) {
    result = kf->reachesAnyOf(bb, path_headers);
  }
  return result;
}

bool LocalExecutor::isPathOverlap(const std::string &first, const std::string &second) const {

  size_t pos = second.find('.', 1);
  while (pos != std::string::npos) {
    std::string tmp = second.substr(0, pos + 1);
    if (boost::algorithm::ends_with(first, tmp)) return true;
    pos = second.find('.', pos + 1);
  }
  return false;
}


bool LocalExecutor::isOnRemainingPath(const ExecutionState &state, const KFunction *kf) const {

  if (state.stack.back().itrace.size() > 0) {

    unsigned fnID = kf->fnID;
    const auto &itr = pathsRemaining.find(fnID);
    if (itr != pathsRemaining.end()) {

      std::stringstream ss;
      ss << '.';
      for (const auto &id : state.stack.back().itrace) {
        ss << id << '.';
      }

      std::string trace = ss.str();
      for (const auto &path : itr->second) {
        if (isPathOverlap(trace, path)) {
          return true;
        }
      }
    }
    return false;
  }
  return true;
}

bool LocalExecutor::removeCoveredRemainingPaths(ExecutionState &state) {

  bool result = false;

  // look through each of the functions covered by this state
  for (auto pr : state.itraces) {
    unsigned fnID = pr.first;
    auto itr = pathsRemaining.find(fnID);

    // if the function has paths remaining...
    if (itr != pathsRemaining.end()) {
      auto &traces = pr.second;
      auto &paths = itr->second;

      auto p_itr = paths.begin();
      while (p_itr != paths.end()) {
        std::string path = *p_itr;
        bool found = false;
        for (const std::string &trace : traces) {
          if (trace.find(path) != std::string::npos) {
            found = true;
            break;
          }
        }
        if (found) {
          p_itr = paths.erase(p_itr);
          result = true;
        }
        else {
          ++p_itr;
        }
      }
    }
  }
  pathsRemaining.clean();
  return result;
}

bool LocalExecutor::addCoveredFaultingPaths(const ExecutionState &state) {

  bool result = false;

  // look through each of the functions covered by this state
  for (auto pr : state.itraces) {
    unsigned fnID = pr.first;
    auto itr = pathsRemaining.find(fnID);

    // if the function has paths remaining...
    if (itr != pathsRemaining.end()) {
      auto &traces = pr.second;
      auto &paths = itr->second;

      auto p_itr = paths.begin();
      while (p_itr != paths.end()) {
        std::string path = *p_itr;
        bool found = false;
        for (const std::string &trace : traces) {
          if (trace.find(path) != std::string::npos) {
            found = true;
            break;
          }
        }
        if (found) {

          // found a missing covered path.  See if this path is already covered by a prior
          // faulting path
          if (!pathsFaulting.contains(fnID, path)) {
            pathsFaulting[fnID].insert(path);
            result = true;
          }
        }
        ++p_itr;
      }
    }
  }
  return result;
}

#endif

ref<ConstantExpr> LocalExecutor::ensureUnique(ExecutionState &state, const ref<Expr> &e) {

  ref<ConstantExpr> result;

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e)) {
    result = CE;
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

#if 0 == 1
  // skip loop accounting if this is the jump from init block
  if (altStartBB != nullptr) {
    // if src and dst bbs have the same parent, then this is a branch
    if (dst->getParent() == src->getParent()) {

      // update the loop frame
      StackFrame &sf = state.stack.back();
      KFunction *kf = sf.kf;

      const llvm::Loop *src_loop = kf->loopInfo.getLoopFor(src);
      const llvm::Loop *dst_loop = kf->loopInfo.getLoopFor(dst);

      if (src_loop == dst_loop) {
        // either source and destination are not in a loop,
        // or they are in the same loop
        if (dst_loop != nullptr) {

         // both in a loop, if the dest is the loop header, then we have completed a cycle
         if (dst_loop->getHeader() == dst && !sf.loopFrames.empty()) {
           LoopFrame &lf = sf.loopFrames.back();
           if (lf.loop == dst_loop) lf.counter += 1;
         }
        }
      } else {
        // source and destination loop are different
        // we either entered a new loop, or exited the previous loop (or both?)
        if (src_loop == nullptr) {

          // entered new loop
          sf.loopFrames.emplace_back(LoopFrame(dst_loop));
        } else if (dst_loop == nullptr) {

          // left the prior loop
          sf.loopFrames.pop_back();
        } else {
          // neither empty implies we just changed loops
          if (src_loop->contains(dst_loop)) {

            // create frames for each intermidiate loop
            const llvm::Loop *curr = dst_loop;
            std::vector<const llvm::Loop*> loops;
            while (curr != src_loop) {
              loops.push_back(curr);
              curr = curr->getParentLoop();
            }
            for (auto itr = loops.rbegin(), end = loops.rend(); itr != end; ++itr) {
              sf.loopFrames.emplace_back(LoopFrame(*itr));
            }

          } else if (dst_loop->contains(src_loop)) {

            // pop loops from frame until we get to the source
            const llvm::Loop *prior = nullptr;
            while (!sf.loopFrames.empty() && prior != src_loop) {
              prior = sf.loopFrames.back().loop;
              sf.loopFrames.pop_back();
            }
          } else {
            klee_error("loop transition between unrelated loops");
          }
        }
      }
    }
  }
#endif
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
        BasicBlock *dst;
#if 0 == 1
        if (altStartBB != nullptr) {
          assert(unconstraintFlags.isUnconstrainLocals());
          dst = const_cast<BasicBlock*>(altStartBB);
        } else {
#endif
          dst = bi->getSuccessor(0);
//        }
        // set alternate start to null after transfer, used as flag
        transferToBasicBlock(state, src, dst);
//        altStartBB = nullptr;

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

            // if we have unconstrained locals, but the destination block cannot reach a remaining
            // path, then there is no point in continuing this state

            if ( false /* unconstraintFlags.isUnconstrainLocals() &&
                !(reachesRemainingPath(kf, dst) || isOnRemainingPath(*states[index], kf) ) */ ) {
              terminateState(*states[index], "remaining paths are unreachable");
            } else {
              transferToBasicBlock(*states[index], src, dst);

              if (bothSatisfyable) {
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
      }
      break;
    }

    case Instruction::Ret: {
      if (libc_initializing &&
          ((state.stack.size() == 0 || !state.stack.back().caller))) {
        libc_initializing = false;
      } else {
        Executor::executeInstruction(state, ki);
      }
      break;
    }

    case Instruction::Invoke:
    case Instruction::Call: {

      const CallSite cs(i);
      std::string fnName = "@unknown";
      bool isInModule = false;
// DELETEME:      bool isMarked = false;
      bool noReturn =  false;
      Function *fn = getTargetFunction(cs.getCalledValue(), state);
      if (fn != nullptr) {
        fnName = fn->getName();

        if (fnName.find("printf") != std::string::npos) {
          Type *ty = cs->getType();
          if (!ty->isVoidTy()) {

            Expr::Width width = kmodule->targetData->getTypeStoreSizeInBits(ty);
            ref<Expr> retExpr = ConstantExpr::create(1, width);
            bindLocal(ki, state, retExpr);
          }
          klee_warning("calling %s", fnName.c_str());
          return;
        }

        isInModule = kmodule->isModuleFunction(fn);
// DELETEME:        if (isInModule) isMarked = kmodule->isMarkedFunction(fn);
        noReturn =  fn->hasFnAttribute(Attribute::NoReturn);

        // if this is a call to a mark() variant, then log the marker to state
        if (kmodule->isMarkerFn(fn)) {
          if ((fn->arg_size() == 2) && fn->getReturnType()->isVoidTy()) {
            const Constant *arg0 = dyn_cast<Constant>(cs.getArgument(0));
            const Constant *arg1 = dyn_cast<Constant>(cs.getArgument(1));
            if ((arg0 != nullptr) && (arg1 != nullptr)) {
              unsigned fnID = (unsigned) arg0->getUniqueInteger().getZExtValue();
              unsigned bbID = (unsigned) arg1->getUniqueInteger().getZExtValue();
              state.addMarker(fnID, bbID);
              assert(false && "should not be any markers");
            }
          }
          return;
        }

        // if this is an intrinsic function, let the standard executor handle it
        if (fn->getIntrinsicID() != Intrinsic::not_intrinsic) {
          Executor::executeInstruction(state, ki);
          return;
        }
      }

      // note that fn can be null in the case of an indirect call
      // if libc is initializing or this is a special function then let the standard executor handle the call
      if (fn == nullptr || libc_initializing || specialFunctionHandler->isSpecial(fn) || kmodule->isInternalFunction(fn)) {
        Executor::executeInstruction(state, ki);
        return;
      }

      // if not stubbing callees and target is in the module
      if (!unconstraintFlags.isStubCallees() && isInModule) {
        if (noReturn /* && !isMarked */) {
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

      // hence, this is a function in this module
      unsigned counter = state.callTargetCounter[fnName]++;

      // consider the arguments pushed for the call, rather than
      // args expected by the target
      unsigned numArgs = cs.arg_size();
      if (fn == nullptr || !fn->isVarArg()) {
        for (unsigned index = 0; index < numArgs; ++index) {
          const Value *v = cs.getArgument(index);
          Type *argType = v->getType();

          // RLR TODO: replace proginfo with equivalent
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

            MemKind kind = MemKind::lazy;

#if 0 == 1
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
                  result = solver->mayBeTrue(state, UltExpr::create(size, min_size));
                }
                if (result) {
                  addConstraint(*sp.second, UltExpr::create(size, min_size));
                  bool success = solver->getValue(*sp.second, size, min_size);
                  assert(success && "FIXME: solver just said mayBeTrue");
                  ref<Expr> eq = EqExpr::create(size, min_size);
                  addConstraint(*sp.second, eq);
                  count = (unsigned) min_size->getZExtValue();
                } else {
                  // too big of an allocation
                  terminateStateOnFault(*sp.second, ki, "zopc_malloc too large");
                  return;
                }
              }
            }
#endif
            // RLR TODO: this is only returning new objects.
            // should it also return existing objects?

            Type *subtype = ty->getPointerElementType();

            // LazyAllocationCount needs to be expanded for string and buffer types.
            unsigned count = LazyAllocationCount;
            if (subtype->isIntegerTy(8) && count < MIN_LAZY_STRING_LEN) {
              count = MIN_LAZY_STRING_LEN;
            }
            MemoryObject *newMO = allocMemory(*sp.second, subtype, i, kind, fullName(fnName, counter, "*0"), 0, count);
            bindObjectInState(*sp.second, newMO);

            ref<ConstantExpr> ptr = newMO->getOffsetIntoExpr(LazyAllocationOffset * (newMO->size / count));
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

      bool to_symbolic = false /*!libc_initializing && unconstraintFlags.isUnconstrainLocals() && !ai->getName().empty() */;
      executeSymbolicAlloc(state, size, 1, ai->getAllocatedType(), MemKind::alloca, ki, to_symbolic);

      break;
    }

    case Instruction::GetElementPtr: {

      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
      ref<Expr> base = eval(ki, 0, state).value;

      if (isUnconstrainedPtr(state, base)) {
        expandLazyAllocation(state, base, true, i->getType(), ki, i->getName());
      } else {

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
            if (solver->mayBeTrue(state, Expr::createIsZero(offset))) {

              // generate a test case
              const KInstruction *prior = state.instFaulting;
              state.instFaulting = ki;
              interpreterHandler->processTestCase(state);
              state.instFaulting = prior;
            }
          }

          ref<Expr> addr = AddExpr::create(base, offset);

          // if we are in zop mode, insure the pointer is inbounds
          if (doAssumeInBounds) {

            Expr::Width width = getWidthForLLVMType(i->getType()->getPointerElementType());
            unsigned bytes = Expr::getMinBytesForWidth(width);

            // base must point into an allocation
            ref<Expr> mc = os->getBoundsCheckPointer(addr, bytes);

            if (!solver->mustBeTrue(state, mc)) {
              if (solver->mayBeTrue(state, mc)) {
                addConstraint(state, mc);
              }
            }
          }

          bindLocal(ki, state, addr);
        } else {

          // invalid memory access, fault at ki and base
          terminateStateOnFault(state, ki, "GEP resolveMO");
        }
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

              // RLR TODO:  type aware allocation size
              destSize *= lazyAllocationCount;
              destSize = std::min(destSize, mo->size);
              if (destSize > os->visible_size) {
                ObjectState *wos = state.addressSpace.getWriteable(mo, os);
                wos->visible_size = destSize;
              }

              // pointed type change
              // RLR TODO: remove type history
//              if (srcPtd != destPtd) {
//
//                // only record if this is a pointer to the beginning of a memory object
//                ref<Expr> is_zero = Expr::createIsZero(mo->getOffsetExpr(ptr));
//
//                if (solver->mayBeTrue(state, is_zero)) {
//                  ObjectState *wos = state.addressSpace.getWriteable(mo, os);
//                  wos->types.insert(destTy);
//                }
//              }
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

Interpreter *Interpreter::createLocal(LLVMContext &ctx,
                                      const InterpreterOptions &opts,
                                      InterpreterHandler *ih) {
  return new LocalExecutor(ctx, opts, ih);
}

}

///

