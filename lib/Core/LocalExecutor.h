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
typedef std::set_ex<ExecutionState*> ExecutionStates;

struct ReplayFnRec {
  const MemoryObject *ret_value;
  std::map<unsigned,const MemoryObject*> param_values;
};

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

  void shutdown() override;
  void bindModule(KModule *kmodule) override;
  void bindModule(KModule *kmodule, ExecutionState *state, uint64_t mem_reserve) override;
  void bindModuleConstants() override;
  void runFunctionAsMain(llvm::Function *f, int argc, char **argv, char **envp) override;
  void runFunctionUnconstrained(llvm::Function *fn) override;
  void runFunctionTestCase(const TestCase &test) override;
  void runMainConcrete(llvm::Function *fn,
                       const std::vector<std::string> &args,
                       const std::vector<unsigned char> &stdin_buffer,
                       llvm::Function *at) override;

  void setPathWriter(TreeStreamWriter *tsw) override { assert(false && "deprectated path writer"); }
  void setSymbolicPathWriter(TreeStreamWriter *tsw) override { assert(false && "deprectated sympath writer"); }
  bool getSymbolicSolution(ExecutionState &state, std::vector<SymbolicSolution> &res, std::vector<ExprSolution> &exprs) override;
  TraceType getTraceType() const override {
    return trace_type;
  }

  const UnconstraintFlagsT *getUnconstraintFlags() override { return &unconstraintFlags; }
  uint64_t getUsedMemory() const override;

protected:
  void runFn(KFunction *kf, std::vector<ExecutionState*> &initialStates);
  ExecutionState *runFnLibCInit(ExecutionState *state);

  void parseBreakAt();
  std::string toSymbolName(const std::string &fn_name, unsigned counter, const std::string &var_name) const {
    return (fn_name + ':' + std::to_string(counter) + ':' + var_name);
  }
  std::string toSymbolName(const std::string &fn_name, unsigned counter, unsigned arg_num) const {
    return toSymbolName(fn_name, counter, std::to_string(arg_num));
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

  MemoryObject *allocMemory(llvm::Type *type,
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

  void unconstrainGlobalVariables(ExecutionState &state, llvm::Function *fn);
  void unconstrainGlobalValues(ExecutionState &state, llvm::Function *fn, unsigned counter);
  void replayGlobalValues(ExecutionState &state, llvm::Function *fn, unsigned counter);
  void unconstrainFnCall(ExecutionState &state, KInstruction *ki, llvm::Function *fn, unsigned counter, ref<Expr> &ret_value);
  void unconstrainFnArg(ExecutionState &state, KInstruction *ki, llvm::Type *type, ref<Expr> &ptr, const std::string &name);
  void replayFnCall(ExecutionState &state, KInstruction *ki, llvm::Function *fn, unsigned counter, ref<Expr> &ret_value);
  void replayFnArg(ExecutionState &state, const MemoryObject *src, const ref<ConstantExpr> &ptr);
  void addReplayValue(const std::string &name, const MemoryObject *mo);
  void loadFnPtrMap(const TestCase *test);

  unsigned countLoadIndirection(const llvm::Type* type) const;
  bool isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e) const;
  bool isReadExpr(ref<Expr> e) const;
  bool isLocallyAllocated(const ExecutionState &state, const MemoryObject *mo) const;
  ref<ConstantExpr> ensureUnique(ExecutionState &state, const ref<Expr> &e);

  void terminateState(ExecutionState &state) override;
  void terminateStateOnMemFault(ExecutionState &state,
                                const KInstruction *ki,
                                ref<Expr> addr,
                                const MemoryObject *mo,
                                const std::string &comment);

  bool getConcreteSolution(ExecutionState &state, std::vector<SymbolicSolution> &result, const std::set_ex<MemKind> &kinds) override;

  const Cell& eval(KInstruction *ki, unsigned index, ExecutionState &state) const override;
  bool addConstraintOrTerminate(ExecutionState &state, ref<Expr> e);
  bool isMainEntry(const llvm::Function *fn) const;
//  void inspectSymbolicSolutions(ExecutionState *state);

  void branch(ExecutionState &state, const std::vector< ref<Expr> > &conditions, std::vector<ExecutionState*> &result) override;
  ExecutionState *clone(ExecutionState *es) override;
  StatePair fork(ExecutionState &current, ref<Expr> condition, bool isInternal) override;

  unsigned lazyAllocationCount;
  unsigned lazyStringLength;
  unsigned maxLazyDepth;
  ExecutionState *baseState;
  uint64_t timeout;
  UnconstraintFlagsT unconstraintFlags;
  std::vector<ProgressionDesc> progression;
  bool libc_initializing;
  bool enable_state_switching;

  std::set_ex<const llvm::Function*> break_fns;
  std::set_ex<unsigned> break_lines;
  ModelOptions optsModel;
  SystemModel *sysModel;
  TraceType trace_type;
  MemoryObject *moStdInBuff;
  ProgramTracer *tracer;
  std::map<llvm::Function *, std::map<unsigned, ReplayFnRec>> replay_stub_data;
  std::map<uint64_t, llvm::Function *> replay_fn_ptrs;

  // behavior conditioned by exec mode
  bool doSaveFault;
  bool doAssumeInBounds;
  bool doLocalCoverage;
  bool doConcreteInterpretation;
  bool doModelStdOutput;
};


} // End klee namespace

#endif
