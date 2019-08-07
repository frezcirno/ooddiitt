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

SplitInitPass::SplitInitPass(KModule *km) : kmodule(km), FunctionPass(ID) {

}

bool SplitInitPass::runOnFunction(Function &F) {

  bool changed = false;
  BasicBlock &entry = F.getEntryBlock();

  // find the first marker call
  for (auto itr = entry.begin(), end = entry.end(); itr != end; ++itr) {

    unsigned opcode = itr->getOpcode();
    if (opcode == Instruction::Call) {
      const CallSite cs(itr);
      if (kmodule->isMarkerFn(cs.getCalledFunction())) {
        entry.splitBasicBlock(itr);
        changed = true;
        break;
      }
    }
  }
  return changed;
}

}
