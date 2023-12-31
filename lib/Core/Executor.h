//===-- Executor.h ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Class to perform actual execution, hides implementation details from external
// interpreter.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXECUTOR_H
#define KLEE_EXECUTOR_H

#include "klee/ExecutionState.h"
#include "klee/Interpreter.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/util/ArrayCache.h"
#include "klee/Internal/ADT/RNG.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/ADT/Twine.h"

#include "klee/Internal/System/Memory.h"

#include <vector>
#include <string>
#include <map>
#include <set>
#include <klee/Internal/Support/ErrorHandling.h>

struct KTest;

namespace llvm {
  class BasicBlock;
  class BranchInst;
  class CallInst;
  class Constant;
  class ConstantExpr;
  class Function;
  class GlobalValue;
  class Instruction;
  class LLVMContext;
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  class TargetData;
#else
  class DataLayout;
#endif
  class Twine;
  class Value;
}

namespace klee {
  class Array;
  struct Cell;
  class ExecutionState;
  class ExternalDispatcher;
  class Expr;
  class InstructionInfoTable;
  struct KFunction;
  struct KInstruction;
  class KInstIterator;
  class KModule;
  class MemoryManager;
  class MemoryObject;
  class ObjectState;
  class PTree;
  class Searcher;
  class SeedInfo;
  class SpecialFunctionHandler;
  struct StackFrame;
  class StatsTracker;
  class TimingSolver;
  class TreeStreamWriter;
  template<class T> class ref;



  /// \todo Add a context object to keep track of data only live
  /// during an instruction step. Should contain addedStates,
  /// removedStates, and haltExecution, among others.

class Executor : public Interpreter {
  friend class BumpMergingSearcher;
  friend class MergingSearcher;
  friend class RandomPathSearcher;
  friend class OwningSearcher;
  friend class WeightedRandomSearcher;
  friend class SpecialFunctionHandler;
  friend class StatsTracker;

public:
  class Timer {
  public:
    Timer();
    virtual ~Timer();

    /// The event callback.
    virtual void run() = 0;
  };

  typedef std::pair<ExecutionState*,ExecutionState*> StatePair;

protected:
  class TimerInfo;

  KModule *kmodule;
  InterpreterHandler *interpreterHandler;
  Searcher *searcher;

  ExternalDispatcher *externalDispatcher;
  TimingSolver *solver;
  MemoryManager *memory;
  std::set<ExecutionState*> states;
  StatsTracker *statsTracker;
  TreeStreamWriter *pathWriter, *symPathWriter;
  SpecialFunctionHandler *specialFunctionHandler;
  std::vector<TimerInfo*> timers;
  PTree *processTree;

  /// Used to track states that have been added during the current
  /// instructions step.
  /// \invariant \ref addedStates is a subset of \ref states.
  /// \invariant \ref addedStates and \ref removedStates are disjoint.
  std::vector<ExecutionState *> addedStates;
  /// Used to track states that have been removed during the current
  /// instructions step.
  /// \invariant \ref removedStates is a subset of \ref states.
  /// \invariant \ref addedStates and \ref removedStates are disjoint.
  std::vector<ExecutionState *> removedStates;

  /// When non-empty the Executor is running in "seed" mode. The
  /// states in this map will be executed in an arbitrary order
  /// (outside the normal search interface) until they terminate. When
  /// the states reach a symbolic branch then either direction that
  /// satisfies one or more seeds will be added to this map. What
  /// happens with other states (that don't satisfy the seeds) depends
  /// on as-yet-to-be-determined flags.
  std::map<ExecutionState*, std::vector<SeedInfo> > seedMap;

  /// Map of globals to their representative memory object.
  std::map<const llvm::GlobalValue*, MemoryObject*> globalObjects;

  /// Map of globals to their bound address. This also includes
  /// globals that have no representative object (i.e. functions).
  std::map<const llvm::GlobalValue*, ref<ConstantExpr> > globalAddresses;

  /// When non-null the bindings that will be used for calls to
  /// klee_make_symbolic in order replay.
  const struct KTest *replayKTest;
  /// When non-null a list of branch decisions to be used for replay.
  const std::vector<bool> *replayPath;
  /// The index into the current \ref replayKTest or \ref replayPath
  /// object.
  unsigned replayPosition;

  /// When non-null a list of "seed" inputs which will be used to
  /// drive execution.
  const std::vector<struct KTest *> *usingSeeds;

  /// Disables forking, instead a random path is chosen. Enabled as
  /// needed to control memory usage. \see fork()
  bool atMemoryLimit;

  /// Disables forking, set by client. \see setInhibitForking()
  bool inhibitForking;

  /// Signals the executor to halt execution at the next instruction
  /// step.
  bool haltExecution;

  /// Whether implied-value concretization is enabled. Currently
  /// false, it is buggy (it needs to validate its writes).
  bool ivcEnabled;

  /// The maximum time to allow for a single core solver query.
  /// (e.g. for a single STP query)
  double coreSolverTimeout;

  /// Assumes ownership of the created array objects
  ArrayCache arrayCache;

  /// File to print executed instructions to
  llvm::raw_ostream *debugInstFile;

  // @brief Buffer used by logBuffer
  std::string debugBufferString;

  // @brief buffer to store logs before flushing to file
  llvm::raw_string_ostream debugLogBuffer;

  std::map<unsigned, unsigned> frequent_forkers;
  std::map<const llvm::Loop *,std::set_ex<const ExecutionState*>> loopingStates;
  unsigned maxStatesInLoop;
  unsigned maxMemInUse;
  unsigned maxSymbolicSize;
  uint64_t maxMemAlloc;

  llvm::Function *getTargetFunction(llvm::Value *calledVal,
                                    ExecutionState &state);

  virtual void executeInstruction(ExecutionState &state, KInstruction *ki);

  void run(ExecutionState &initialState);

  // Given a concrete object in our [klee's] address space, add it to
  // objects checked code can reference.
  MemoryObject *addExternalObject(ExecutionState &state,
                                  const void *addr,
                                  unsigned size,
                                  const llvm::Type *type,
                                  const llvm::Value *allocSite,
                                  unsigned align,
                                  bool isReadOnly = false);

  void initializeGlobalObject(ExecutionState &state, ObjectState *os,
                              const llvm::Constant *c,
                              unsigned offset);
  void initializeGlobals(ExecutionState &state);
  void reinitializeGlobals(ExecutionState &state);
  MemoryObject *findGlobalObject(const std::string &name) const {
    if (llvm::GlobalValue *gv = kmodule->getGlobalVariable(name)) {
      return findGlobalObject(gv);
    }
    return nullptr;
  }

  MemoryObject *findGlobalObject(const llvm::GlobalValue *gv) const {
    auto itr = globalObjects.find(gv);
    if (itr != globalObjects.end()) {
      return itr->second;
    }
    return nullptr;
  }


  void stepInstruction(ExecutionState &state);
  virtual void updateStates(ExecutionState *current);
  virtual void transferToBasicBlock(ExecutionState &state, llvm::BasicBlock *src, llvm::BasicBlock *dst);

  void callExternalFunction(ExecutionState &state,
                            KInstruction *target,
                            llvm::Function *function,
                            std::vector< ref<Expr> > &arguments);

  ObjectState *bindObjectInState(ExecutionState &state, const MemoryObject *mo, const Array *array = nullptr);

  /// Resolve a pointer to the memory objects it could point to the
  /// start of, forking execution when necessary and generating errors
  /// for pointers to invalid locations (either out of bounds or
  /// address inside the middle of objects).
  ///
  /// \param results[out] A list of ((MemoryObject,ObjectState),
  /// state) pairs for each object the given address can point to the
  /// beginning of.
  typedef std::vector< std::pair<std::pair<const MemoryObject*, const ObjectState*>,
                                 ExecutionState*> > ExactResolutionList;
  void resolveExact(ExecutionState &state,
                    ref<Expr> p,
                    ExactResolutionList &results,
                    const std::string &name);

  /// Allocate and bind a new object in a particular state. NOTE: This
  /// function may fork.
  ///
  /// \param isLocal Flag to indicate if the object should be
  /// automatically deallocated on function return (this also makes it
  /// illegal to free directly).
  ///
  /// \param target Value at which to bind the base address of the new
  /// object.
  ///
  /// \param reallocFrom If non-zero and the allocation succeeds,
  /// initialize the new object from the given one and unbind it when
  /// done (realloc semantics). The initialized bytes will be the
  /// minimum of the size of the old and new objects, with remaining
  /// bytes initialized as specified by zeroMemory.
  void executeDynamicAlloc(ExecutionState &state,
                           ref<Expr> size,
                           MemKind kind,
                           KInstruction *target,
                           bool zeroMemory=false,
                           const ObjectState *reallocFrom=0);

  /// Free the given address with checking for errors. If target is
  /// given it will be bound to 0 in the resulting states (this is a
  /// convenience for realloc). Note that this function can cause the
  /// state to fork and that \ref state cannot be safely accessed
  /// afterwards.
  virtual void executeFree(ExecutionState &state,
                           ref<Expr> address,
                           KInstruction *target = 0);

  void executeCall(ExecutionState &state,
                   KInstruction *ki,
                   llvm::Function *f,
                   std::vector< ref<Expr> > &arguments);

  // do address resolution / object binding / out of bounds checking
  // and perform the operation
  virtual void executeMemoryOperation(ExecutionState &state,
                                      bool isWrite,
                                      ref<Expr> address,
                                      ref<Expr> value /* undef if read */,
                                      KInstruction *target /* undef if write */);

  void executeMakeSymbolic(ExecutionState &state, const MemoryObject *mo,
                           const std::string &name);

  /// Create a new state where each input condition has been added as
  /// a constraint and return the results. The input state is included
  /// as one of the results. Note that the output vector may included
  /// NULL pointers for states which were unable to be created.
  virtual void branch(ExecutionState &state, const std::vector< ref<Expr> > &conditions, std::vector<ExecutionState*> &result);
  virtual  ExecutionState *clone(ExecutionState *es);

  // Fork current and return states in which condition holds / does
  // not hold, respectively. One of the states is necessarily the
  // current state, and one of the states may be null.
  virtual StatePair fork(ExecutionState &current, ref<Expr> condition, bool isInternal);

  /// Add the given (boolean) condition as a constraint on state. This
  /// function is a wrapper around the state's addConstraint function
  /// which also manages propagation of implied values,
  /// validity checks, and seed patching.
  void addConstraint(ExecutionState &state, ref<Expr> condition);

  // Called on [for now] concrete reads, replaces constant with a symbolic
  // Used for testing.
  ref<Expr> replaceReadWithSymbolic(ExecutionState &state, ref<Expr> e);

  virtual const Cell& eval(KInstruction *ki, unsigned index,
                           ExecutionState &state) const;

  Cell& getArgumentCell(ExecutionState &state,
                        KFunction *kf,
                        unsigned index) {
    return state.stack.back().locals[kf->getArgRegister(index)];
  }

  Cell& getDestCell(ExecutionState &state,
                    KInstruction *target) {
    return state.stack.back().locals[target->dest];
  }

  void bindLocal(KInstruction *target,
                 ExecutionState &state,
                 ref<Expr> value);
  void bindArgument(KFunction *kf,
                    unsigned index,
                    ExecutionState &state,
                    ref<Expr> value);

  ref<klee::ConstantExpr> evalConstantExpr(const llvm::ConstantExpr *ce);

  /// Return a unique constant value for the given expression in the
  /// given state, if it has one (i.e. it provably only has a single
  /// value). Otherwise return the original expression.
  ref<Expr> toUnique(const ExecutionState &state, ref<Expr> &e);

  /// Return a constant value for the given expression, forcing it to
  /// be constant in the given state by adding a constraint if
  /// necessary. Note that this function breaks completeness and
  /// should generally be avoided.
  ///
  /// \param purpose An identify string to printed in case of concretization.
  ref<klee::ConstantExpr> toConstant(ExecutionState &state, ref<Expr> e, const char *purpose);
  ref<klee::ConstantExpr> toConstantMin(ExecutionState &state, ref<Expr> e, const char *purpose);
  ref<klee::ConstantExpr> toConstantFP(ExecutionState &state, ref<Expr> e, const char *purpose);

  ref<klee::ConstantExpr> toExample(ExecutionState &state, ref<Expr> e);

  /// Bind a constant value for e to the given target. NOTE: This
  /// function may fork state if the state has multiple seeds.
  void executeGetValue(ExecutionState &state, ref<Expr> e, KInstruction *target);

  /// Get textual information regarding a memory address.
  std::string getAddressInfo(ExecutionState &state, ref<Expr> address) const;

  // Determines the \param lastInstruction of the \param state which is not KLEE
  // internal and returns its InstructionInfo
  const InstructionInfo & getLastNonKleeInternalInstruction(const ExecutionState &state, llvm::Instruction** lastInstruction);

  // remove state from queue and delete
  virtual void terminateState(ExecutionState &state);
  // call exit handler and terminate state

  void terminateStateOnComplete(ExecutionState &state, TerminateReason reason);

  void terminateStateOnComplete(ExecutionState &state, TerminateReason reason, const std::string &comment)
    { state.messages.push_back(comment); terminateStateOnComplete(state, reason); }

  // Discarded states may still be persisted as test cases by dump-states-on-halt
  // Disposed states are gone, gone, gone
  void terminateStateOnDiscard(ExecutionState &state, const std::string &comment);
  void terminateStateOnDispose(ExecutionState &state, const std::string &comment);
  void terminateStateOnDecimate(ExecutionState &state);

  /// bindModuleConstants - Initialize the module constant table.
  virtual void bindModuleConstants();

  template <typename TypeIt>
  void computeOffsets(KGEPInstruction *kgepi, TypeIt ib, TypeIt ie);

  /// bindInstructionConstants - Initialize any necessary per instruction
  /// constant values.
  void bindInstructionConstants(KInstruction *KI);

  void doImpliedValueConcretization(ExecutionState &state,
                                    ref<Expr> e,
                                    ref<ConstantExpr> value);

  /// Add a timer to be executed periodically.
  ///
  /// \param timer The timer object to run on firings.
  /// \param rate The approximate delay (in seconds) between firings.
  void addTimer(Timer *timer, double rate);

  void initTimers();
  void processTimers(ExecutionState *current, double maxInstTime);
  virtual void checkMemoryUsage();
  void printDebugInstructions(ExecutionState &state);
  void doDumpStates();

  bool isOnlyInLoop(const ExecutionState *state, const KFunction *kf, const llvm::Loop *loop) const;
  bool isInLoop(const ExecutionState *state, const KFunction *kf, const llvm::Loop *loop) const;
  void tryCmdPreference(ExecutionState &state, const MemoryObject *mo);
  void tryStrPreference(ExecutionState &state, const MemoryObject *mo);
  bool tryPreferenceValue(ExecutionState &state, char ch, ref<Expr> value);
  bool tryPreferenceRange(ExecutionState &state, char ch1, char ch2, ref<Expr> value);

  bool mustBeInRange(ExecutionState &state, unsigned char ch1, unsigned char ch2, ref<Expr> value) const;
  bool mustBeDigit(ExecutionState &state, ref<Expr> value) const { return mustBeInRange(state, '0', '9', value); }
  bool mustBeLowerLetter(ExecutionState &state, ref<Expr> value) const { return mustBeInRange(state, 'a', 'z', value); }
  bool mustBeUpperLetter(ExecutionState &state, ref<Expr> value) const { return mustBeInRange(state, 'A', 'Z', value); }
  bool mustBeLetter(ExecutionState &state, ref<Expr> value) const {
    return mustBeLowerLetter(state, value) || mustBeUpperLetter(state, value);
  }

  bool tryInRangeValue(ExecutionState &state, unsigned char ch1, unsigned char ch2, ref<Expr> value);
  bool tryDigitValue(ExecutionState &state, ref<Expr> value) { return tryInRangeValue(state, '0', '9', value); }
  bool tryLowerLetterValue(ExecutionState &state, ref<Expr> value) { return tryInRangeValue(state, 'a', 'z', value); }
  bool tryUpperLetterValue(ExecutionState &state, ref<Expr> value) { return tryInRangeValue(state, 'A', 'Z', value); }
  bool tryLetterValue(ExecutionState &state, ref<Expr> value) {
    return tryLowerLetterValue(state, value) || tryUpperLetterValue(state, value);
  }

  bool isUnique(const ExecutionState &state, ref<Expr> &e) const;

public:
  Executor(llvm::LLVMContext &ctx, const InterpreterOptions &opts, InterpreterHandler *ie);
  ~Executor() override;

  void shutdown() override;

  const InterpreterHandler& getHandler() {
    return *interpreterHandler;
  }

  // XXX should just be moved out to utility module
  ref<klee::ConstantExpr> evalConstant(const llvm::Constant *c);

  void setPathWriter(TreeStreamWriter *tsw) override {
    pathWriter = tsw;
  }
  void setSymbolicPathWriter(TreeStreamWriter *tsw) override {
    symPathWriter = tsw;
  }

  void setReplayKTest(const struct KTest *out) override {
    assert(!replayPath && "cannot replay both buffer and path");
    replayKTest = out;
    replayPosition = 0;
  }

  void setReplayPath(const std::vector<bool> *path) override {
    assert(!replayKTest && "cannot replay both buffer and path");
    replayPath = path;
    replayPosition = 0;
  }

  void bindModule(KModule *kmodule) override;

  void useSeeds(const std::vector<struct KTest *> *seeds) override {
    usingSeeds = seeds;
  }

  void runFunctionAsMain(llvm::Function *f, int argc, char **argv, char **envp) override;

  /*** Runtime options ***/

  void setHaltExecution(bool value) override {
    haltExecution = value;
  }

  void setInhibitForking(bool value) override {
    inhibitForking = value;
  }

  void prepareForEarlyExit() override;

  /*** State accessor methods ***/

  unsigned getPathStreamID(const ExecutionState &state) override;

  unsigned getSymbolicPathStreamID(const ExecutionState &state) override;

  void getConstraintLog(const ExecutionState &state, std::string &res, LogType logFormat) override;
  bool getSymbolicSolution(ExecutionState &state, std::vector<SymbolicSolution> &res) override;

  void getCoveredLines(const ExecutionState &state, std::map<const char*, std::set<unsigned> > &res) override;

  Expr::Width getWidthForLLVMType(LLVM_TYPE_Q llvm::Type *type) const;
  size_t getAllocationAlignment(const llvm::Value *allocSite) const;

  KModule *getKModule() const override { return kmodule; }
  void getGlobalVariableMap(std::map<const llvm::GlobalVariable*,MemoryObject*> &objects) override;


  void log_warning(const std::string &msg) override { klee_warning("%s", msg.c_str()); }
  void log_warning(const std::string &msg, ExecutionState &state) override { state.messages.push_back(msg); log_warning(msg); };
  void log_warning(const std::string &msg, ExecutionState &state, KInstruction *ki) override
    { std::ostringstream ss; ss << msg << " (location:" << ki->info->assemblyLine << ')'; log_warning(ss.str(), state); };

  void log_warning(const std::ostringstream &ss) { log_warning(ss.str()); }
  void log_warning(const std::ostringstream &ss, ExecutionState &state) { log_warning(ss.str(), state); }
  void log_warning(const std::ostringstream &ss, ExecutionState &state, KInstruction *ki) { log_warning(ss.str(), state, ki); }
};

} // End klee namespace

#endif
