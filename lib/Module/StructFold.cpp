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
#include <klee/Internal/Module/ModuleTypes.h>
#include <regex>

using namespace llvm;
using namespace std;

namespace klee {

char StructFoldPass::ID = 0;

bool StructFoldPass::runOnModule(Module &module) {

  static regex re("(struct\\..*)\\.(\\d+)");
  map<string,set<StructType*> > baseTypes;

  set<StructType*> types;
  ModuleTypes finder(&module, types);

  // reduce structure types to a set of base types
  for (StructType *type : types) {
    if (type->hasName()) {
      const string name = type->getName();
      smatch matches;
      if (regex_match(name, matches, re)) {
        baseTypes[matches[1]].insert(type);
      }
    }
  }

  for (const auto &pr : baseTypes) {
    if (areAllEquivalent(pr.second)) {
    } else {
      outs() << pr.first << ": ";
      for (StructType *type : pr.second) {
        outs() << type->getName() << ", ";
        type->setName(pr.first);
      }
      outs() << oendl;
    }
  }
  return false;
}

bool StructFoldPass::areAllEquivalent(const std::set<llvm::StructType*> &types) const {

  assert(!types.empty());
  StructType *first = nullptr;
  for (StructType *type : types) {
    if (first == nullptr) {
      first = type;
    } else {
      if (!first->isLayoutIdentical(type)) {
        return false;
      }
    }
  }
  return true;
};

};
