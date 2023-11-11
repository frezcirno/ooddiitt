//===-- ClangInfo.h -----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#pragma once

#include <string>
#include <map>
#include <vector>

namespace klee {

class ClangFnArgInfo {
  bool is_const;

public:
  ClangFnArgInfo() : is_const(false){};
  void setConst(bool b = true) { is_const = b; }
  bool isConst() const { return is_const; }
};

class ClangFunctionInfo {
  std::vector<ClangFnArgInfo> arg_info;

public:
  ClangFunctionInfo() = default;
  void setNumArgs(unsigned num) { arg_info.resize(num); }
  unsigned arg_size() const { return arg_info.size(); }
  ClangFnArgInfo &getArg(unsigned num) { return arg_info.at(num); }
};

class ClangProgInfo {
  std::map<std::string, ClangFunctionInfo> fn_info;

public:
  ClangFunctionInfo &addFn(std::string name) { return fn_info[name]; }
  ClangFunctionInfo &addFn(std::string name, unsigned num) {
    auto &info = fn_info[name];
    info.setNumArgs(num);
    return info;
  }
  bool empty() const { return fn_info.empty(); }
  ClangFunctionInfo *getFn(std::string name) {
    auto itr = fn_info.find(name);
    if (itr != fn_info.end()) return &itr->second;
    return nullptr;
  }
};

} // end klee namespace
