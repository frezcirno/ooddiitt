//===-- ExecutionState.h ----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_TESTCASE_H
#define KLEE_TESTCASE_H

#include <map>
#include <set>
#include <vector>

namespace klee {

class TestObject {
public:
  TestObject(std::string _addr, unsigned _count, std::string _data, std::string _kind, std::string _name, std::string _type) :
    addr(_addr), count(_count), data(_data), kind(_kind), name(_name), type(_type) {}

  std::string addr;
  unsigned count;
  std::string data;
  std::string kind;
  std::string name;
  std::string type;
};

class TestCase {
public:

  TestCase() : arg_c(0), lazy_alloc_count(0), max_lazy_depth(0), max_loop_forks(0), max_loop_iter(0), test_id(UINT_MAX) {}
  bool is_ready() { return test_id != UINT_MAX; }


  int arg_c;
  std::string arg_v;
  std::string entry_fn;
  std::string klee_version;
  unsigned lazy_alloc_count;
  unsigned max_lazy_depth;
  unsigned max_loop_forks;
  unsigned max_loop_iter;
  std::string message;
  std::string path_condition_vars;
  std::string status;
  unsigned test_id;
  std::deque<TestObject> objects;
};

}

#endif
