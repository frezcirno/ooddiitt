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
  void runFunctionUnconstrained(llvm::Function *f) override;
  void runFunctionTestCase(const TestCase &test) override;
  ExecutionState *runLibCInitializer(ExecutionState &state, llvm::Function *f);

  void setPathWriter(TreeStreamWriter *tsw) override { assert(false && "deprectated path writer"); }
  void setSymbolicPathWriter(TreeStreamWriter *tsw) override { assert(false && "deprectated sympath writer"); }

protected:
  void runFn(KFunction *kf, std::vector<ExecutionState*> &initialStates);
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
  void checkMemoryFnUsage(KFunction *kf = nullptr);
  unsigned numStatesInLoop(const llvm::Loop *loop) const;
  unsigned decimateStatesInLoop(const llvm::Loop *loop, unsigned skip_counter = 0);
  bool addConstraintOrTerminate(ExecutionState &state, ref<Expr> e);
  bool isMainEntry(const llvm::Function *fn) const;
  void InspectSymbolicSolutions(const ExecutionState *state);

  unsigned lazyAllocationCount;
  unsigned maxLoopIteration;
  unsigned maxLoopForks;
  unsigned maxLazyDepth;
  std::set<ExecutionState*> faulting_state_stash;
  std::map<const llvm::Loop*, unsigned> loopForkCounter;
  unsigned maxStatesInLoop;
  ExecutionState *baseState;
  uint64_t timeout;
  UnconstraintFlagsT unconstraintFlags;
  std::vector<ProgressionDesc> progression;
  bool libc_initializing;
  bool enable_state_switching;

#ifdef _DEBUG
  std::set<const llvm::Function*> break_fns;
  std::set<unsigned> break_lines;
#endif

  // behavior conditioned by exec mode
  bool doSaveFault;
  bool doAssumeInBounds;
  bool doLocalCoverage;
  bool doConcreteInterpretation;
};


} // End klee namespace

#endif
