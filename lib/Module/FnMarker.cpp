//===-- PhiCleaner.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Passes.h"

#include <set>

using namespace llvm;
namespace klee {

char FnMarkerPass::ID = 0;

bool FnMarkerPass::doInitialization(llvm::Module &module) {

  mdkind_fnID = module.getMDKindID("brt-klee.fnID");
  mdkind_bbID = module.getMDKindID("brt-klee.bbID");
  return false;
}

bool FnMarkerPass::runOnFunction(Function &f) {

  LLVMContext &ctx = f.getContext();
  unsigned next_bbID = 1;

  for (Function::iterator b = f.begin(), be = f.end(); b != be; ++b) {
    BasicBlock &bb = *b;
    if (!bb.empty()) {
      Instruction &inst = bb.front();
      MDNode *md = MDNode::get(ctx, MDString::get(ctx, std::to_string(next_bbID)));
      inst.setMetadata(mdkind_bbID, md);
      if (next_bbID == 1) {
        md = MDNode::get(ctx, MDString::get(ctx, std::to_string(next_fnID)));
        inst.setMetadata(mdkind_fnID, md);
      }
      next_bbID += 1;
    }
  }
  next_fnID += 1;
  return false;
}

bool FnMarkerPass::doFinalization(llvm::Module &module) {


  return false;
}

};
