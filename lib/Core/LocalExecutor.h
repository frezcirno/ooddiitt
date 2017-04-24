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

namespace klee {

class LocalExecutor : public Executor {

public:
  static Interpreter *create(llvm::LLVMContext &ctx,
                             const InterpreterOptions &opts,
                             InterpreterHandler *ih,
                             const std::set<llvm::Function *> fns)
    { return new klee::LocalExecutor(ctx, opts, ih, fns); }
  
  LocalExecutor(llvm::LLVMContext &ctx,
                const InterpreterOptions &opts,
                InterpreterHandler *ie,
                const std::set<llvm::Function *> &fns);

  virtual ~LocalExecutor();
  
  virtual void runFunctionAsMain(llvm::Function *f,
                                 int argc,
                                 char **argv,
                                 char **envp);
  virtual void runFunctionUnconstrained(llvm::Function *f);

protected:
  virtual void run(ExecutionState &initialState);

  std::string fullName(std::string fnName, unsigned counter, std::string varName) const {
    return (fnName + "::" + std::to_string(counter) + "::" + varName);
  }

  virtual void executeInstruction(ExecutionState &state, KInstruction *ki);

  bool resolveMO(ExecutionState &state, ref<Expr> address, ObjectPair &op);
  
  bool executeReadMemoryOperation(ExecutionState &state,
                                  ref<Expr> address,
                                  const llvm::Type *type,
                                  KInstruction *target);

  bool executeWriteMemoryOperation(ExecutionState &state,
                                   ref<Expr> address,
                                   ref<Expr> value,
                                   const std::string name);
  
  ObjectState *makeSymbolic(ExecutionState &state,
                            const MemoryObject *mo,
                            const ObjectState *os = nullptr);

  MemoryObject *allocMemory(ExecutionState &state,
                            unsigned count,
                            llvm::Type *type,
                            size_t align,
                            const llvm::Value *allocSite,
                            bool isGlobal,
                            std::string name);

  MemoryObject *allocMemory(ExecutionState &state,
                            size_t size,
                            size_t align,
                            const llvm::Value *allocSite,
                            bool isGlobal,
                            std::string name);

  ref<Expr> allocSymbolic(ExecutionState &state,
                          size_t size,
                          size_t align,
                          const llvm::Value *allocSite,
                          bool isGlobal,
                          std::string name,
                          ObjectPair &op);

  ref<Expr> allocSymbolic(ExecutionState &state,
                          unsigned count,
                          llvm::Type *type,
                          size_t align,
                          const llvm::Value *allocSite,
                          bool isGlobal,
                          std::string name);

  unsigned countLoadIndirection(const llvm::Type* type) const;
  
  bool isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e);

  unsigned lazyAllocationCount;
  unsigned iterationBound;
  const std::set<llvm::Function *> &fnInModule;
};
  
} // End klee namespace

#endif
