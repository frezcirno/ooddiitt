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
#include "SystemModel.h"

namespace klee {

typedef std::pair<MemoryObject*,ObjectState*> WObjectPair;
typedef std::set<ExecutionState*> ExecutionStates;

class LocalExecutor : public Executor {

  friend class SpecialFunctionHandler;
  friend class SystemModel;

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

  ~LocalExecutor() override;

  void bindModule(KModule *kmodule) override;
  void bindModuleConstants() override;
  void runFunctionAsMain(llvm::Function *f, int argc, char **argv, char **envp) override;
  void runFunctionUnconstrained(llvm::Function *fn) override;
  void runFunctionTestCase(const TestCase &test) override;
  void runMainConcrete(llvm::Function *fn,
                       const std::vector<std::string> &args,
                       const std::vector<unsigned char> &stdin_buffer,
                       llvm::Function *at) override;

  ExecutionState *runLibCInitializer(ExecutionState &state, llvm::Function *f);

  void setPathWriter(TreeStreamWriter *tsw) override { assert(false && "deprectated path writer"); }
  void setSymbolicPathWriter(TreeStreamWriter *tsw) override { assert(false && "deprectated sympath writer"); }
  bool getSymbolicSolution(const ExecutionState &state, std::vector<SymbolicSolution> &res, std::vector<ExprSolution> &exprs) override;
  TraceType getTraceType() const override {
    return trace_type;
  }

  const UnconstraintFlagsT *getUnconstraintFlags() override { return &unconstraintFlags; }

protected:
  void runFn(KFunction *kf, std::vector<ExecutionState*> &initialStates);
  std::string fullName(std::string fnName, unsigned counter, std::string varName) const {
    return (fnName + "::" + std::to_string(counter) + "::" + varName);
  }

  void executeInstruction(ExecutionState &state, KInstruction *ki) override;
  void transferToBasicBlock(ExecutionState &state, llvm::BasicBlock *src, llvm::BasicBlock *dst) override;

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

  MemoryObject *injectMemory(ExecutionState &state,
                             void *addr,
                             const std::vector<unsigned char> &data,
                             const std::string &type_desc,
                             MemKind kind,
                             const std::string &name,
                             unsigned count);

  void expandLazyAllocation(ExecutionState &state,
                            ref<Expr> addr,
                            const llvm::Type *type,
                            KInstruction *target,
                            const std::string &name,
                            bool allow_null);

  bool allocSymbolic(ExecutionState &state,
                     llvm::Type *type,
                     const llvm::Value *allocSite,
                     MemKind kind,
                     const std::string &name,
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
  bool isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e) const;
  bool isReadExpr(ref<Expr> e) const;
  bool isLocallyAllocated(const ExecutionState &state, const MemoryObject *mo) const;
  ref<ConstantExpr> ensureUnique(ExecutionState &state, const ref<Expr> &e);
  bool isUnique(const ExecutionState &state, ref<Expr> &e) const;

  void terminateState(ExecutionState &state) override;
  void terminateStateOnMemFault(ExecutionState &state,
                                const KInstruction *ki,
                                ref<Expr> addr,
                                const MemoryObject *mo,
                                const std::string &comment);

  bool getConcreteSolution(ExecutionState &state, std::vector<SymbolicSolution> &result, const std::set<MemKind> &kinds) override;

  const Cell& eval(KInstruction *ki, unsigned index, ExecutionState &state) const override;
  bool addConstraintOrTerminate(ExecutionState &state, ref<Expr> e);
  bool isMainEntry(const llvm::Function *fn) const;
  void InspectSymbolicSolutions(const ExecutionState *state);
  bool isLegalFunction(const llvm::Function *fn) const {
    return legalFunctions.find((uint64_t) fn) != legalFunctions.end();
  }
  void checkMemoryUsage() override;

  void branch(ExecutionState &state, const std::vector< ref<Expr> > &conditions, std::vector<ExecutionState*> &result) override;
  ExecutionState *clone(ExecutionState *es) override;
  StatePair fork(ExecutionState &current, ref<Expr> condition, bool isInternal) override;

  unsigned lazyAllocationCount;
  unsigned lazyStringLength;
  unsigned maxLazyDepth;
  unsigned maxStatesInLoop;
  ExecutionState *baseState;
  uint64_t timeout;
  UnconstraintFlagsT unconstraintFlags;
  std::vector<ProgressionDesc> progression;
  bool libc_initializing;
  bool enable_state_switching;

  std::set<const llvm::Function*> break_fns;
  std::set<unsigned> break_lines;
  ModelOptions optsModel;
  SystemModel *sysModel;
  TraceType trace_type;
  MemoryObject *moStdInBuff;
  ProgramTracer *tracer;
  std::map<const llvm::Loop *, ExecutionStates> loopingStates;
  bool isOnlyInLoop(ExecutionState *state, KFunction *kf, const llvm::Loop *loop);
  bool isInLoop(ExecutionState *state, KFunction *kf, const llvm::Loop *loop);

  // behavior conditioned by exec mode
  bool doSaveFault;
  bool doAssumeInBounds;
  bool doLocalCoverage;
  bool doConcreteInterpretation;
  bool doModelStdOutput;
};


} // End klee namespace

#endif
