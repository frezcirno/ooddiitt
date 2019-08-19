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

#include "Executor.h"
#include "klee/Internal/System/Memory.h"
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
  void runFunctionUnconstrained(llvm::Function *f, unsigned starting_marker) override;
  ExecutionState *runLibCInitializer(ExecutionState &state, llvm::Function *f);

protected:
  void runFn(KFunction *kf, ExecutionState &initialState, unsigned starting_marker);
  void runFnEachBlock(KFunction *kf, ExecutionState &initialState);
  HaltReason runFnFromBlock(KFunction *kf, ExecutionState &initialState, const llvm::BasicBlock *start);

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
                                   const std::string &name);

  ObjectState *makeSymbolic(ExecutionState &state,
                            const MemoryObject *mo);

  MemoryObject *allocMemory(ExecutionState &state,
                            llvm::Type *type,
                            const llvm::Value *allocSite,
                            MemKind kind,
                            const std::string &name,
                            size_t align = 0,
                            unsigned count = 1);

  void expandLazyAllocation(ExecutionState &state,
                            ref<Expr> addr,
                            bool restart,
                            const llvm::Type *type,
                            KInstruction *target,
                            const std::string &name);

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

  void unconstrainGlobals(ExecutionState &state, llvm::Function *fn);
  void newUnconstrainedGlobalValues(ExecutionState &state, llvm::Function *fn, unsigned counter);

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
  void transferToBasicBlock(ExecutionState &state, llvm::BasicBlock *src, llvm::BasicBlock *dst);
  void checkMemoryFnUsage(KFunction *kf = nullptr);
  unsigned numStatesInLoop(const llvm::Loop *loop) const;
  unsigned decimateStatesInLoop(const llvm::Loop *loop, unsigned skip_counter = 0);

  void getReachablePaths(const std::string &fn_name, M2MPaths &paths, bool transClosure) const;
  void getAllPaths(M2MPaths &paths) const;
  bool reachesRemainingPath(const KFunction *kf, const llvm::BasicBlock *bb) const;
  bool isOnRemainingPath(const ExecutionState &state, const KFunction *kf) const;
  bool isPathOverlap(const std::string &first, const std::string &second) const;
  bool removeCoveredRemainingPaths(ExecutionState &state);
  bool addCoveredFaultingPaths(const ExecutionState &state);

  bool addConstraintOrTerminate(ExecutionState &state, ref<Expr> e);
  void InspectSymbolicSolutions(const ExecutionState *state);

  unsigned lazyAllocationCount;
  unsigned maxLoopIteration;
  unsigned maxLoopForks;
  unsigned maxLazyDepth;
  M2MPaths pathsRemaining;
  M2MPaths pathsFaulting;
  std::set<ExecutionState*> faulting_state_stash;
  std::map<const llvm::Loop*, unsigned> loopForkCounter;
  ProgInfo *progInfo;
  unsigned maxStatesInLoop;
  ExecutionState *baseState;
  void *heap_base;
  uint64_t timeout;
  UnconstraintFlagsT unconstraintFlags;
  std::vector<ProgressionDesc> progression;
  bool libc_initializing;
  const llvm::BasicBlock *altStartBB;

  // behavior conditioned by exec mode
  bool doSaveComplete;
  bool doSaveFault;
  bool doAssumeInBounds;
  bool doLocalCoverage;
  bool timeout_disabled;
};


} // End klee namespace

#endif
