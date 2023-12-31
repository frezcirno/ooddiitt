//===-- ModuleUtil.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_TRANSFORM_UTIL_H
#define KLEE_TRANSFORM_UTIL_H

#include <string>
#include <set>

namespace llvm {
  class Function;
  class Instruction;
  class Module; 
  class CallSite; 
  class GlobalVariable;
}

namespace klee {
  struct IndirectCallRewriteRec {
    IndirectCallRewriteRec(const std::string &t, const std::string &s) : target(t), sig(s) {}
    std::string target;
    std::string sig;
    std::set<std::string> scope;
  };
  typedef std::vector<IndirectCallRewriteRec> IndirectCallRewriteRecs;

  /// Link a module with a specified bitcode archive.
  llvm::Module *linkWithLibrary(llvm::Module *module, 
                                const std::string &libraryName);

  /// Return the Function* target of a Call or Invoke instruction, or
  /// null if it cannot be determined (should be only for indirect
  /// calls, although complicated constant expressions might be
  /// another possibility).
  ///
  /// If `moduleIsFullyLinked` is set to true it will be assumed that the
  //  module containing the `llvm::CallSite` is fully linked. This assumption
  //  allows resolution of functions that are marked as overridable.
  llvm::Function *getDirectCallTarget(llvm::CallSite, bool moduleIsFullyLinked);

  /// Return true iff the given Function value is used in something
  /// other than a direct call (or a constant expression that
  /// terminates in a direct call).
  bool functionEscapes(const llvm::Function *f);

  void enumModuleFunctions(llvm::Module *m, std::set<llvm::Function*> &fns);
  void enumModuleGlobals(llvm::Module *m, std::set<llvm::GlobalVariable*> &gbs);
  void enumModuleVisibleDefines(llvm::Module *m, std::set<llvm::Function*> &fns, std::set<llvm::GlobalVariable*> &gbs);
  llvm::Module *rewriteFunctionPointers(llvm::Module *m, const IndirectCallRewriteRecs &recs);
  bool isPrepared(llvm::Module *m);
  void modify_clib(llvm::Module *m);
}

#endif
