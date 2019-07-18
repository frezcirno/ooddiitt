//===-- SplitInit.cpp - Split fn entry block into initialization and remainer blocks -------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// splits fn entry block into two, first only initializes (and is unmarked)
//
//===----------------------------------------------------------------------===//

#include "Passes.h"
#include "llvm/IR/LLVMContext.h"
#include <llvm/Support/CallSite.h>
#include "klee/Config/Version.h"
#include <algorithm>

using namespace llvm;

namespace klee {

char SplitInitPass::ID = 0;

SplitInitPass::SplitInitPass(KModule *km) : FunctionPass(ID) {

  for (std::string fn_name : km->getFnMarkers()) {
    Function *fn = km->module->getFunction(fn_name);
    if (fn != nullptr) {
      if ((fn->arg_size() == 2) && (fn->getReturnType()->isVoidTy())) {
        markerFunctions.insert(fn);
      }
    }
  }
}

bool SplitInitPass::runOnFunction(Function &F) {

  bool changed = false;
  BasicBlock &entry = F.getEntryBlock();

  // find the first marker call
  for (auto itr = entry.begin(), end = entry.end(); itr != end; ++itr) {

    unsigned opcode = itr->getOpcode();
    if (opcode == Instruction::Call) {
      const CallSite cs(itr);
      if (markerFunctions.count(cs.getCalledFunction()) > 0) {
        entry.splitBasicBlock(itr);
        changed = true;
        break;
      }
    }
  }
  return changed;
}

}
