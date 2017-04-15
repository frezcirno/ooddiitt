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
                                      KInstruction *target);
  
  bool executeFastWriteMemoryOperation(ExecutionState &state,
                                       ref<Expr> address,
                                       ref<Expr> value);

  void makeSymbolic(ExecutionState &state,
                    const MemoryObject *mo);
  
};
  
} // End klee namespace

#endif
