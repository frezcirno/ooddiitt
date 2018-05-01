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
#include "llvm/Analysis/Dominators.h"
#include "tuple"

namespace klee {

typedef std::pair<MemoryObject*,ObjectState*> WObjectPair;
typedef std::set<ExecutionState*> ExecutionStates;

class LocalExecutor : public Executor {

public:

  enum class HaltReason { OK, TimeOut, InvalidExpr };
  enum class ResolveResult { OK, NullAccess, NoObject };

  static Interpreter *create(llvm::LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih,
                             ProgInfo *progInfo)
    { return new klee::LocalExecutor(ctx, opts, ih, progInfo); }
  
  LocalExecutor(llvm::LLVMContext &ctx,
                const InterpreterOptions &opts,
                InterpreterHandler *ie,
                ProgInfo *progInfo);

  virtual ~LocalExecutor();

  virtual const llvm::Module *setModule(llvm::Module *module, const ModuleOptions &opts);
  virtual void bindModuleConstants();

  virtual void runFunctionAsMain(llvm::Function *f,
                                 int argc,
                                 char **argv,
                                 char **envp);
  virtual void runFunctionUnconstrained(llvm::Function *f);

protected:
  void runFn(KFunction *kf, ExecutionState &initialState);
  void runPaths(KFunction *kf, ExecutionState &initialState);
  HaltReason runFrom(KFunction *kf, ExecutionState &initialState, const llvm::BasicBlock *start);
  void prepareLocalSymbolics(KFunction *kf, ExecutionState &initialState);

  std::string fullName(std::string fnName, unsigned counter, std::string varName) const {
    return (fnName + "::" + std::to_string(counter) + "::" + varName);
  }

  virtual void executeInstruction(ExecutionState &state, KInstruction *ki);

  ResolveResult resolveMO(ExecutionState &state, ref<Expr> address, ObjectPair &op);

  void executeAlloc(ExecutionState &state,
                    unsigned size,
                    unsigned count,
                    const llvm::Type *type,
                    MemKind kind,
                    KInstruction *target,
                    bool symbolic = false);


  virtual void executeFree(ExecutionState &state,
                           ref<Expr> address,
                           KInstruction *target = 0);

  bool executeReadMemoryOperation(ExecutionState &state,
                                  ref<Expr> address,
                                  const llvm::Type *type,
                                  KInstruction *target);

  bool executeWriteMemoryOperation(ExecutionState &state,
                                   ref<Expr> address,
                                   ref<Expr> value,
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
  bool isUsherType(const llvm::Type *type) const;

  unsigned countLoadIndirection(const llvm::Type* type) const;
  bool isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e);
  bool isLocallyAllocated(const ExecutionState &state, const MemoryObject *mo) const;
  ref<ConstantExpr> ensureUnique(ExecutionState &state, const ref<Expr> &e);
  bool isUnique(const ExecutionState &state, ref<Expr> &e) const;
  void terminateState(ExecutionState &state) override;
  void terminateStateOnExit(ExecutionState &state) override;
  void terminateStateEarly(ExecutionState &state, const llvm::Twine &message) override;
  void terminateStateOnError(ExecutionState &state, const llvm::Twine &message,
                                     enum TerminateReason termReason,
                                     const char *suffix = NULL,
                                     const llvm::Twine &longMessage = "") override;


  virtual const Cell& eval(KInstruction *ki, unsigned index, ExecutionState &state) const;
  void updateStates(ExecutionState *current) override;
  void transferToBasicBlock(llvm::BasicBlock *dst, llvm::BasicBlock *src, ExecutionState &state) override;
  unsigned getNextLoopSignature() { return ++nextLoopSignature; }
  void checkMemoryFnUsage(KFunction *kf = nullptr);
  unsigned numStatesInLoop(const llvm::BasicBlock *hdr) const;
  unsigned decimateStatesInLoop(const llvm::BasicBlock *hdr, unsigned skip_counter = 0);
  unsigned numStatesWithLoopSig(unsigned loopSig) const;
  bool coversPath(const m2m_paths_t &paths, const ExecutionState *state) const;
  void getCoveredPaths(const m2m_paths_t &paths, const ExecutionState *state, m2m_paths_t &covered) const;
  bool reachesRemainingPath(KFunction *kf, const llvm::BasicBlock *bb) const;
  void updateCoveredPaths(const ExecutionState *state);
  bool addConstraintOrTerminate(ExecutionState &state, ref<Expr> e);

  void InspectSymbolicSolutions(const ExecutionState *state);

#ifdef NEVER
  // RLR TODO: remove this after debugging is complete (i.e., long after I am 6 ft deep...)
  uint64_t getAddr(ExecutionState& state, ref<Expr> addr) const;
  int64_t getValue(ExecutionState& state, ref<Expr> value) const;
#endif

  unsigned lazyAllocationCount;
  unsigned maxLoopIteration;
  unsigned maxLoopForks;
  unsigned maxLazyDepth;
  m2m_paths_t m2m_pathsRemaining;
  m2m_paths_t m2m_pathsCovered;
  ExecutionStates stowedStates;
  m2m_paths_t m2m_pathsCoveredByStowed;
  unsigned nextLoopSignature;
  std::map<const llvm::BasicBlock*, unsigned> forkCounter;
  ProgInfo *progInfo;
  unsigned seMaxTime;
  unsigned maxStatesInLoop;
  ExecutionState *germinalState;
  void *heap_base;
};


} // End klee namespace

#endif
