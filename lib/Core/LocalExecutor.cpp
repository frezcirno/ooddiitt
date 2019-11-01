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
#define MIN_LAZY_STRING_LEN 9

using namespace llvm;
using namespace std;

namespace klee {

#define countof(a) (sizeof(a)/ sizeof(a[0]))

class bad_expression : public std::runtime_error
{
public:
  bad_expression() : std::runtime_error("null expression") {}
  bad_expression(const char *msg) : std::runtime_error(msg) {}
};


class Tracer {
  virtual unsigned to_entry(KInstruction *ki);
};


cl::opt<unsigned> SymArgs("sym-args", cl::init(0), cl::desc("Maximum number of command line arguments"));
cl::opt<bool> VerifyConstraints("verify-constraints", cl::init(false), cl::desc("Perform additional constraint verification before adding"));
cl::opt<bool> SavePendingStates("save-pending-states", cl::init(true), cl::desc("at timeout, save states that have not completed"));
cl::opt<unsigned> LazyAllocationCount("lazy-allocation-count", cl::init(1), cl::desc("Number of items to lazy initialize pointer"));
cl::opt<unsigned> LazyAllocationOffset("lazy-allocation-offset", cl::init(0), cl::desc("index into lazy allocation to return"));
cl::opt<unsigned> MinLazyAllocationSize("lazy-allocation-minsize", cl::init(0), cl::desc("minimum size of a lazy allocation"));
cl::opt<unsigned> LazyAllocationDepth("lazy-allocation-depth", cl::init(4), cl::desc("Depth of items to lazy initialize pointer"));
cl::opt<unsigned> LazyAllocationExt("lazy-allocation-ext", cl::init(0), cl::desc("number of lazy allocations to include existing memory objects of same type"));
cl::opt<unsigned> MaxLoopIteration("max-loop-iteration", cl::init(4), cl::desc("Number of loop iterations"));
cl::opt<unsigned> MaxLoopForks("max-loop-forks", cl::init(16), cl::desc("Number of forks within loop body"));
cl::opt<bool> TraceAssembly("trace-assm", cl::init(false), cl::desc("trace assembly lines"));
cl::opt<bool> TraceStatements("trace-stmt", cl::init(false), cl::desc("trace source lines (does not capture filename)"));
cl::opt<bool> TraceBBlocks("trace-bblk", cl::init(false), cl::desc("trace basic block markers"));
cl::opt<string> BreakAt("break-at", cl::desc("break at the given trace line number or function name"));

LocalExecutor::LocalExecutor(LLVMContext &ctx, const InterpreterOptions &opts, InterpreterHandler *ih) :
  Executor(ctx, opts, ih),
  lazyAllocationCount(LazyAllocationCount),
  maxLoopIteration(MaxLoopIteration),
  maxLoopForks(MaxLoopForks),
  maxLazyDepth(LazyAllocationDepth),
  maxStatesInLoop(10000),
  baseState(nullptr),
  progression(opts.progression),
  libc_initializing(false) {

  switch (opts.mode) {
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
    default:
      klee_error("invalid execution mode");
  }

  optsModel.doModelStdOutput = doModelStdOutput;
  sysModel = new SystemModel(this, optsModel);

  Executor::setVerifyContraints(VerifyConstraints);
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
    // this last state is leaked.  something in solver
    // tear-down does not like its deletion
//    delete baseState;
    baseState = nullptr;

  }
}

void LocalExecutor::getModeledExternals(std::set<std::string> &names) const {
  Executor::getModeledExternals(names);
  if (sysModel != nullptr) {
    sysModel->GetModeledExternals(names);
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
  // RLR TODO: disable bitcode constants
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
  offsetExpr = toUnique(state, offsetExpr);
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
        outs() << "RLR: Does this ever actually happen?\n";
        os = makeSymbolic(*currState, mo);
      }
    }
  }

  ref<Expr> e = os->read(offsetExpr, width);
  bindLocal(target, *currState, e);

  if ((countLoadIndirection(type) > 1) && isUnconstrainedPtr(*currState, e)) {

    // give a meaningful name to the symbolic variable.
    // do not have original c field names, so use field index
    string name = mo->name;
    if (const StructType *st = dyn_cast<StructType>(mo->type)) {
      if (isa<ConstantExpr>(offsetExpr)) {
        unsigned offset = cast<ConstantExpr>(offsetExpr)->getZExtValue();
        const StructLayout *targetStruct = kmodule->targetData->getStructLayout(const_cast<StructType*>(st));
        unsigned index = targetStruct->getElementContainingOffset(offset);
        name += ':' + std::to_string(index);
      }
    }

    // this is an unconstrained ptr-ptr.
    expandLazyAllocation(state, e, type->getPointerElementType(), target, name);
  }
  return true;
}

void LocalExecutor::expandLazyAllocation(ExecutionState &state,
                                         ref<Expr> addr,
                                         const llvm::Type *type,
                                         KInstruction *target,
                                         const std::string &name) {

  assert(type->isPointerTy());

  Type *base_type = type->getPointerElementType();
  if (base_type->isFirstClassType()) {

    // count current depth of lazy allocations
    unsigned depth = 0;
    for (auto end = (unsigned) name.size(); depth < end && name.at(depth) == '*'; ++depth);

    ref<ConstantExpr> null = Expr::createPointer(0);
    ref<Expr> eqNull = EqExpr::create(addr, null);

    if (depth >= maxLazyDepth) {

      // too deep. no more forking for this pointer.
      addConstraintOrTerminate(state, eqNull);

    } else {

      StatePair sp = fork(state, eqNull, true);

      // in the true case, ptr is null, so nothing further to do
      ExecutionState *next_fork = sp.second;

      // in the false case, allocate new memory for the ptr and
      // constrain the ptr to point to it.
      if (next_fork != nullptr) {

        // pointer may not be null
        if (LazyAllocationExt > 0) {

          unsigned counter = 0;

          // consider any existing objects in memory of the same type
          std::vector<ObjectPair> listOPs;
          sp.second->addressSpace.getMemoryObjects(listOPs, base_type);
          for (const auto &pr : listOPs) {

            if (next_fork == nullptr || counter >= LazyAllocationExt)
              break;

            const MemoryObject *existingMO = pr.first;
            if (existingMO->kind == MemKind::lazy) {

              // fork a new state
              ref<ConstantExpr> ptr = existingMO->getBaseExpr();
              ref<Expr> eq = EqExpr::create(addr, ptr);
              StatePair sp2 = fork(*next_fork, eq, true);
              counter += 1;
              next_fork = sp2.second;
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
        }
      }
    }
  } else if (base_type->isFunctionTy()) {
    // RLR TODO: do something here!
    // just say NO to function pointers
    ref<Expr> eqNull = EqExpr::create(addr, Expr::createPointer(0));
    addConstraintOrTerminate(state, eqNull);
  } else {
    klee_warning("lazy initialization of unknown type: %s", to_string(base_type).c_str());
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

  set<string> *globals = interpreterOpts.userGlobals;
  string fn_name = fn->getName();
  for (auto itr = kmodule->module->global_begin(), end = kmodule->module->global_end(); itr != end; ++itr) {
    const GlobalVariable *v = static_cast<const GlobalVariable *>(itr);
    if (v->hasName()) {
      string gv_name = v->getName().str();
      if (globals != nullptr) {
        if (globals->find(gv_name) == globals->end()) continue; // next global
      } else {
        if (v->isConstant() || v->hasHiddenVisibility())  continue; // next global
      }

      auto pos = gv_name.find('.');
      // if dot in first position or the prefix does not equal the function name, continue to next variable
      if (pos == 0) continue;
      if (pos != string::npos && (fn_name != gv_name.substr(0, pos))) continue;

      MemoryObject *mo = globalObjects.find(v)->second;
      if (mo != nullptr) {

        outs() << "unconstraining: " << gv_name << '\n';

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

const Module *LocalExecutor::setModule(llvm::Module *module, const ModuleOptions &opts) {

  assert(kmodule == nullptr);
  const Module *result = Executor::setModule(module, opts);
  specialFunctionHandler->setLocalExecutor(this);

  // prepare a generic initial state
  baseState = new ExecutionState();
  baseState->maxLoopIteration = maxLoopIteration;
  baseState->lazyAllocationCount = lazyAllocationCount;
  baseState->maxLazyDepth = maxLazyDepth;
  baseState->maxLoopForks = maxLoopForks;

  initializeGlobals(*baseState);
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

        // and the remainder of the argv array should be null
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

#if 0 == 1
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

    ObjectPair op = state->addressSpace.findMemoryObjectByName("output_delimiter_specified");
    if (op.first != nullptr) {
      ObjectState *wos = state->addressSpace.getWriteable(op.first, op.second);
      wos->write8(0, 1);
    }
  }

  init_states.push_back(state);
  runFn(kf, init_states);
#endif

}

void LocalExecutor::runFn(KFunction *kf, std::vector<ExecutionState*> &init_states) {

  assert(!init_states.empty());
  Function *fn = kf->function;

  outs() << fn->getName().str() << ": " << interpreterHandler->flags_to_string(unconstraintFlags) << '\n';
  outs().flush();

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
          klee_warning("break at element %s not found", line.c_str());
        }
      }
    }
  }

  ProgramTracer *tracer = nullptr;
  if (TraceBBlocks) {
//    if (interpreterOpts.userFns != nullptr) tracer = new BBlocksTracer(kmodule, interpreterOpts.userFns);
    tracer = new BBlocksTracer(kmodule);
  } else if (TraceAssembly) {
    tracer = new AssemblyTracer;
  } else if (TraceStatements) {
    tracer = new StatementTracer;
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
    checkMemoryFnUsage(kf);
  }

  loopForkCounter.clear();
  for (ExecutionState *state : states) {
    if (SavePendingStates) {
      interpreterHandler->processTestCase(*state);
    }
    terminateState(*state, "flushing states on halt");
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

  // RLR TODO: now consider our stashed faulting states?
  faulting_state_stash.clear();

  // RLR TODO: save pending states as well...
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

  if (state.status == StateStatus::Completed) {
    interpreterHandler->processTestCase(state);
  } else if (state.status == StateStatus::Faulted) {
    interpreterHandler->processTestCase(state);
  } else {
    // its an error state, pending state, or discarded state
    // stash faults for later consideration
  }
  Executor::terminateState(state, message);
}

void LocalExecutor::terminateStateOnExit(ExecutionState &state) {
  state.status = StateStatus::Completed;
  Executor::terminateStateOnExit(state);
}

void LocalExecutor::terminateStateOnFault(ExecutionState &state, const KInstruction *ki, const llvm::Twine &message) {
  state.status = StateStatus::Faulted;
  state.instFaulting = ki;
  state.terminationMessage = message.str();
  terminateState(state, message);
}

void LocalExecutor::terminateStateEarly(ExecutionState &state, const llvm::Twine &message) {
  state.status = StateStatus::TerminateEarly;
  Executor::terminateStateEarly(state, message);
}

void LocalExecutor::terminateStateOnError(ExecutionState &state, const llvm::Twine &message,
                           enum TerminateReason termReason,
                           const char *suffix,
                           const llvm::Twine &longMessage) {
  state.status = StateStatus::TerminateError;
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

          // get loop id
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
          state->status = StateStatus::Decimated;
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
      bool noReturn =  false;
      Function *fn = getTargetFunction(cs.getCalledValue(), state);
      if (fn != nullptr) {
        fnName = fn->getName();

        isInModule = kmodule->isModuleFunction(fn);
        noReturn =  fn->hasFnAttribute(Attribute::NoReturn);

        // if this is an intrinsic function, let the standard executor handle it
        if (fn->getIntrinsicID() != Intrinsic::not_intrinsic) {
          Executor::executeInstruction(state, ki);
          return;
        }
      } else {
        // cannot find target function
        // likely because its a fn pointer

      }


      if (break_fns.find(fn) != break_fns.end()) {
        outs() << "break at " << fn->getName() << '\n';
#ifdef _DEBUG
        enable_state_switching = false;
#endif
      }

      // invoke model of posix functions
      if (sysModel != nullptr) {
        ref<Expr> retExpr;
        if (sysModel->Execute(state, fn, ki, cs, retExpr)) {
          // the system model handled the call
          if (!retExpr.isNull()) bindLocal(ki, state, retExpr);
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
      klee_warning("stubbing function %s", fnName.c_str());

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

            // RLR TODO: this is only returning new objects.
            // should it also return existing objects?

            Type *base_type = ty->getPointerElementType();

            // LazyAllocationCount needs to be expanded for string and buffer types.
            unsigned count = LazyAllocationCount;
            if (base_type->isIntegerTy(8) && count < MIN_LAZY_STRING_LEN) {
              count = MIN_LAZY_STRING_LEN;
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
      executeSymbolicAlloc(state, size, 1, ai->getAllocatedType(), MemKind::alloca_l, ki, to_symbolic);

      break;
    }

    case Instruction::GetElementPtr: {

      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
      ref<Expr> base = eval(ki, 0, state).value;
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
      assert(!isUnconstrainedPtr(state, base));

#if 0 == 1
      if (isUnconstrainedPtr(state, base)) {
        outs() << "RLR TODO: Debug this\n";
        state.restartInstruction();
        expandLazyAllocation(state, base, i->getType(), ki, i->getName());
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
#endif
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

Interpreter *Interpreter::createLocal(LLVMContext &ctx,
                                      const InterpreterOptions &opts,
                                      InterpreterHandler *ih) {
  return new LocalExecutor(ctx, opts, ih);
}

}

///

