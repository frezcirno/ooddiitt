//===-- KModule.h -----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Metadata.h"
#include "llvm/IR/Constants.h"

#include <set>
#include <vector>

namespace klee {

class MDBuilder {

  llvm::LLVMContext &ctx;

public:
  MDBuilder(llvm::LLVMContext &_ctx) : ctx(_ctx) {}
  llvm::MDNode *create(const std::string &str) { return llvm::MDNode::get(ctx, llvm::MDString::get(ctx, str)); }
  llvm::MDNode *create(unsigned num) {
    llvm::Value *v = llvm::ConstantInt::get(llvm::Type::getInt32Ty(ctx), num);
    return llvm::MDNode::get(ctx, v);
  }

  llvm::MDNode *create(const std::set<const llvm::GlobalVariable *> &s) {
    std::vector<llvm::Value *> values;
    values.reserve(s.size());
    for (auto &v : s) {
      values.emplace_back((llvm::Value *)v);
    }
    return llvm::MDNode::get(ctx, values);
  }

  llvm::MDNode *create(const std::set<const llvm::Function *> &s) {
    std::vector<llvm::Value *> values;
    values.reserve(s.size());
    for (auto &v : s) {
      values.emplace_back((llvm::Value *)v);
    }
    return llvm::MDNode::get(ctx, values);
  }

  llvm::MDNode *create(llvm::Function *fn, const std::set<unsigned> &idxs) {
    std::vector<llvm::Value *> values;
    values.reserve(idxs.size() + 1);
    values.emplace_back((llvm::Value *)fn);
    for (auto idx : idxs) {
      values.emplace_back(llvm::ConstantInt::get(llvm::Type::getInt32Ty(ctx), idx));
    }
    return llvm::MDNode::get(ctx, values);
  }

};

} // end klee namespace
