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

#ifndef KLEE_LOCAL_EXECUTOR_H
#define KLEE_LOCAL_EXECUTOR_H

#include "TimedSolver.h"
#include "Executor.h"
#include "klee/Internal/System/Memory.h"
#include "llvm/Analysis/Dominators.h"
#include "tuple"

namespace klee {

typedef std::pair<MemoryObject*,ObjectState*> WObjectPair;
typedef std::set<ExecutionState*> ExecutionStates;

class LocalExecutor : public Executor {

  friend class SpecialFunctionHandler;

public:

  enum class HaltReason { OK, TimeOut, InvalidExpr };
  enum class ResolveResult { OK, NullAccess, NoObject };

  static Interpreter *create(llvm::LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih)
    { return new klee::LocalExecutor(ctx, opts, ih); }
  
  LocalExecutor(llvm::LLVMContext &ctx,
                const InterpreterOptions &opts,
                InterpreterHandler *ie);

  virtual ~LocalExecutor();

  const llvm::Module *setModule(llvm::Module *module, const ModuleOptions &opts) override;
  void bindModuleConstants() override;
  void runFunctionAsMain(llvm::Function *f, int argc, char **argv, char **envp) override;
  void runFunctionUnconstrained(llvm::Function *f) override;

protected:
  void runFn(KFunction *kf, ExecutionState &initialState);
  void runFnEachBlock(KFunction *kf, ExecutionState &initialState);
  HaltReason runFnFromBlock(KFunction *kf, ExecutionState &initialState, const llvm::BasicBlock *start);
  void prepareLocalSymbolics(KFunction *kf, ExecutionState &initialState);

  std::string fullName(std::string fnName, unsigned counter, std::string varName) const {
    return (fnName + "::" + std::to_string(counter) + "::" + varName);
  }

  void executeInstruction(ExecutionState &state, KInstruction *ki) override;

  ResolveResult resolveMO(ExecutionState &state, ref<Expr> address, ObjectPair &op);

  void executeSymbolicAlloc(ExecutionState &state,
                            unsigned size,
                            unsigned count,
                            const llvm::Type *type,
                            MemKind kind,
                            KInstruction *target,
                            bool symbolic = false);

  void executeFree(ExecutionState &state, ref<Expr> address, KInstruction *target) override;

  bool executeReadMemoryOperation(ExecutionState &state,
                                  ref<Expr> address,
                                  const llvm::Type *type,
                                  KInstruction *target);

  bool executeWriteMemoryOperation(ExecutionState &state,
                                   ref<Expr> address,
                                   ref<Expr> value,
                                   KInstruction *target,
                                   const std::string name);
  
  ObjectState *makeSymbolic(ExecutionState &state,
                            const MemoryObject *mo);

  MemoryObject *allocMemory(ExecutionState &state,
                            llvm::Type *type,
                            const llvm::Value *allocSite,
                            MemKind kind,
                            std::string name,
                            size_t align = 0,
                            unsigned count = 1);

  bool allocSymbolic(ExecutionState &state,
                     llvm::Type *type,
                     const llvm::Value *allocSite,
                     MemKind kind,
                     std::string name,
                     WObjectPair &wop,
                     size_t align = 0,
                     unsigned count = 1);


  bool duplicateSymbolic(ExecutionState &state,
                         const MemoryObject *mo,
                         const llvm::Value *allocSite,
                         std::string name,
                         WObjectPair &wop);

  void initializeGlobalValues(ExecutionState &state, llvm::Function *fn);
  void unconstrainGlobals(ExecutionState &state, llvm::Function *fn, unsigned counter);

  unsigned countLoadIndirection(const llvm::Type* type) const;
  bool isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e);
  bool isLocallyAllocated(const ExecutionState &state, const MemoryObject *mo) const;
  ref<ConstantExpr> ensureUnique(ExecutionState &state, const ref<Expr> &e);
  bool isUnique(const ExecutionState &state, ref<Expr> &e) const;
  void terminateState(ExecutionState &state, const llvm::Twine &message) override;
  void terminateStateOnExit(ExecutionState &state) override;
  void terminateStateOnFault(ExecutionState &state, const KInstruction *ki, const llvm::Twine &message);
  void terminateStateEarly(ExecutionState &state, const llvm::Twine &message) override;
  void terminateStateOnError(ExecutionState &state,
                             const llvm::Twine &message,
                             enum TerminateReason termReason,
                             const char *suffix = nullptr,
                             const llvm::Twine &longMessage = "") override;

  const Cell& eval(KInstruction *ki, unsigned index, ExecutionState &state) const override;
  void transferToBasicBlock(llvm::BasicBlock *dst, llvm::BasicBlock *src, ExecutionState &state) override;
  unsigned getNextLoopSignature() { return ++nextLoopSignature; }
  void checkMemoryFnUsage(KFunction *kf = nullptr);
  unsigned numStatesInLoop(const llvm::BasicBlock *hdr) const;
  unsigned decimateStatesInLoop(const llvm::BasicBlock *hdr, unsigned skip_counter = 0);
  unsigned numStatesWithLoopSig(unsigned loopSig) const;

  void getReachablePaths(const KFunction *kf, M2MPaths &paths);
  bool reachesRemainingPath(const KFunction *kf, const llvm::BasicBlock *bb) const;
  bool removeCoveredRemainingPaths(const ExecutionState *state);

  bool addConstraintOrTerminate(ExecutionState &state, ref<Expr> e);
  void InspectSymbolicSolutions(const ExecutionState *state);

  TimedSolver *tsolver;
  unsigned lazyAllocationCount;
  unsigned maxLoopIteration;
  unsigned maxLoopForks;
  unsigned maxLazyDepth;
  M2MPaths pathsRemaining;
  unsigned nextLoopSignature;
  std::map<const llvm::BasicBlock*, unsigned> forkCounter;
  ProgInfo *progInfo;
  unsigned maxStatesInLoop;
  ExecutionState *germinalState;
  void *heap_base;
  uint64_t timeout;
  UnconstraintFlagsT unconstraintFlags;
  std::vector<ProgressionDesc> progression;

  // behavior conditioned by exec mode
  bool doSaveComplete;
  bool doSaveFault;
  bool doAssumeInBounds;
  bool doLocalCoverage;
  bool verbose;
};


} // End klee namespace

#endif
