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
                             InterpreterHandler *ih) { return new klee::LocalExecutor(ctx, opts, ih); }
  
  LocalExecutor(llvm::LLVMContext &ctx,
                const InterpreterOptions &opts,
                InterpreterHandler *ie);
  virtual ~LocalExecutor();
  
  virtual void runFunctionAsMain(llvm::Function *f,
                                 int argc,
                                 char **argv,
                                 char **envp);
  virtual void runFunctionUnconstrained(llvm::Function *f);

protected:
  virtual void run(ExecutionState &initialState);
  
  virtual void executeInstruction(ExecutionState &state, KInstruction *ki);
  
  bool executeFastReadMemoryOperation(ExecutionState &state,
                                      ref<Expr> address,
                                      const llvm::Type *type,
                                      KInstruction *target);
  
  bool executeFastWriteMemoryOperation(ExecutionState &state,
                                       ref<Expr> address,
                                       ref<Expr> value,
                                       const std::string name);

  void executeReadMemoryOperation(ExecutionState &state,
                                  ref<Expr> address,
                                  const llvm::Type *type,
                                  KInstruction *target);

  void executeWriteMemoryOperation(ExecutionState &state,
                                   ref<Expr> address,
                                   ref<Expr> value,
                                   const std::string name);
  
  ObjectState *makeSymbolic(ExecutionState &state,
                            const MemoryObject *mo,
                            const ObjectState *os = nullptr);
  
  unsigned countLoadIndirection(const llvm::Type* type) const;
  
  bool isUnconstrainedPtr(const ExecutionState &state, ref<Expr> e);
  
  
  unsigned lazyAllocationCount;
};
  
} // End klee namespace

#endif
