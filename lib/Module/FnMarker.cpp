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
  mapFn.clear();
  mapBB.clear();
  return false;
}

bool FnMarkerPass::runOnFunction(Function &fn) {

  LLVMContext &ctx = fn.getContext();
  unsigned next_bbID = 1;

  for (Function::iterator b = fn.begin(), be = fn.end(); b != be; ++b) {
    BasicBlock &bb = *b;
    if (!bb.empty()) {
      Instruction &inst = bb.front();
      MDNode *md = MDNode::get(ctx, MDString::get(ctx, std::to_string(next_bbID)));
      inst.setMetadata(mdkind_bbID, md);
      mapBB[&bb] = next_bbID;

      md = MDNode::get(ctx, MDString::get(ctx, std::to_string(next_fnID)));
      inst.setMetadata(mdkind_fnID, md);
      if (next_bbID == 1) {
        mapFn[&fn] = next_fnID;
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
