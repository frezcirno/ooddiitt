//===-- Passes.h ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_PASSES_H
#define KLEE_PASSES_H

#include "klee/Config/Version.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/Triple.h"
#include "llvm/CodeGen/IntrinsicLowering.h"
#include "llvm/Pass.h"

#include <klee/Internal/Module/KModule.h>

#include <set>
#include <llvm/Support/CallSite.h>

namespace llvm {
  class Function;
  class Instruction;
  class Module;
  class DataLayout;
  class TargetLowering;
  class Type;
}

namespace klee {

  /// RaiseAsmPass - This pass raises some common occurences of inline
  /// asm which are used by glibc into normal LLVM IR.
class RaiseAsmPass : public llvm::ModulePass {
  static char ID;

  const llvm::TargetLowering *TLI;

  llvm::Triple triple;

  llvm::Function *getIntrinsic(llvm::Module &M,
                               unsigned IID,
                               LLVM_TYPE_Q llvm::Type **Tys,
                               unsigned NumTys);
  llvm::Function *getIntrinsic(llvm::Module &M,
                               unsigned IID, 
                               LLVM_TYPE_Q llvm::Type *Ty0) {
    return getIntrinsic(M, IID, &Ty0, 1);
  }

  bool runOnInstruction(llvm::Module &M, llvm::Instruction *I);

public:
  RaiseAsmPass() : llvm::ModulePass(ID), TLI(0) {}
  
  virtual bool runOnModule(llvm::Module &M);
};

  // This is a module pass because it can add and delete module
  // variables (via intrinsic lowering).
class IntrinsicCleanerPass : public llvm::ModulePass {
  static char ID;
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  const llvm::TargetData &TargetData;
#else
  const llvm::DataLayout &DataLayout;
#endif
  llvm::IntrinsicLowering *IL;
  bool LowerIntrinsics;

  bool runOnBasicBlock(llvm::BasicBlock &b, llvm::Module &M);
public:
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  IntrinsicCleanerPass(const llvm::TargetData &TD,
#else
  IntrinsicCleanerPass(const llvm::DataLayout &TD,
#endif
                       bool LI=true)
    : llvm::ModulePass(ID),
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
      TargetData(TD),
#else
      DataLayout(TD),
#endif
      IL(new llvm::IntrinsicLowering(TD)),
      LowerIntrinsics(LI) {}
  ~IntrinsicCleanerPass() { delete IL; } 
  
  virtual bool runOnModule(llvm::Module &M);
};
  
  // performs two transformations which make interpretation
  // easier and faster.
  //
  // 1) Ensure that all the PHI nodes in a basic block have
  //    the incoming block list in the same order. Thus the
  //    incoming block index only needs to be computed once
  //    for each transfer.
  // 
  // 2) Ensure that no PHI node result is used as an argument to
  //    a subsequent PHI node in the same basic block. This allows
  //    the transfer to execute the instructions in order instead
  //    of in two passes.
class PhiCleanerPass : public llvm::FunctionPass {
  static char ID;

public:
  PhiCleanerPass() : llvm::FunctionPass(ID) {}
  
  virtual bool runOnFunction(llvm::Function &f);
};
  
class DivCheckPass : public llvm::ModulePass {
  static char ID;
public:
  DivCheckPass(): ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
};

/// This pass injects checks to check for overshifting.
///
/// Overshifting is where a Shl, LShr or AShr is performed
/// where the shift amount is greater than width of the bitvector
/// being shifted.
/// In LLVM (and in C/C++) this undefined behaviour!
///
/// Example:
/// \code
///     unsigned char x=15;
///     x << 4 ; // Defined behaviour
///     x << 8 ; // Undefined behaviour
///     x << 255 ; // Undefined behaviour
/// \endcode
class OvershiftCheckPass : public llvm::ModulePass {
  static char ID;
public:
  OvershiftCheckPass(): ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
};

/// LowerSwitchPass - Replace all SwitchInst instructions with chained branch
/// instructions.  Note that this cannot be a BasicBlock pass because it
/// modifies the CFG!
class LowerSwitchPass : public llvm::FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  LowerSwitchPass() : FunctionPass(ID) {} 
  
  virtual bool runOnFunction(llvm::Function &F);
  
  struct SwitchCase {
    llvm ::Constant *value;
    llvm::BasicBlock *block;
    
    SwitchCase() : value(0), block(0) { }
    SwitchCase(llvm::Constant *v, llvm::BasicBlock *b) :
      value(v), block(b) { }
  };
  
  typedef std::vector<SwitchCase>           CaseVector;
  typedef std::vector<SwitchCase>::iterator CaseItr;
  
private:
  void processSwitchInst(llvm::SwitchInst *SI);
  void switchConvert(CaseItr begin,
                     CaseItr end,
                     llvm::Value *value,
                     llvm::BasicBlock *origBlock,
                     llvm::BasicBlock *defaultBlock);
};

/// InstructionOperandTypeCheckPass - Type checks the types of instruction
/// operands to check that they conform to invariants expected by the Executor.
///
/// This is a ModulePass because other pass types are not meant to maintain
/// state between calls.
class InstructionOperandTypeCheckPass : public llvm::ModulePass {
private:
  bool instructionOperandsConform;

public:
  static char ID;
  InstructionOperandTypeCheckPass()
      : llvm::ModulePass(ID), instructionOperandsConform(true) {}
  bool runOnModule(llvm::Module &M) override;
  bool checkPassed() const { return instructionOperandsConform; }
};

class FnMarkerPass : public llvm::FunctionPass {
  static char ID;

public:
  FnMarkerPass(std::map<const llvm::Function*,unsigned> &_mapFn,
               std::map<const llvm::BasicBlock*, unsigned> &_mapBB,
               const std::set<llvm::Function*> &_fns) :
        llvm::FunctionPass(ID),
        mdkind_fnID(0),
        mdkind_bbID(0),
        next_fnID(1),
        mapFn(_mapFn),
        mapBB(_mapBB),
        fns(_fns) {}
  bool runOnFunction(llvm::Function &f) override;
  bool doInitialization(llvm::Module &module) override;
  bool doFinalization(llvm::Module &module) override;
private:
  unsigned mdkind_fnID;
  unsigned mdkind_bbID;
  unsigned next_fnID;
  std::map<const llvm::Function*,unsigned> &mapFn;
  std::map<const llvm::BasicBlock*, unsigned> &mapBB;
  const std::set<llvm::Function*> &fns;
};

class StructFoldPass : public llvm::ModulePass {
  static char ID;
public:
  StructFoldPass(): ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
private:
  bool areAllEquivalent(const std::set<llvm::StructType*> &types) const;
};

}

#endif
