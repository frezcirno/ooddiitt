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
#include <chrono>
#include <sstream>
#include <iomanip>
#include <boost/endian/conversion.hpp>
#include "klee/util/CommonUtil.h"

typedef std::chrono::system_clock sys_clock;

namespace klee {

class TestObject {
public:
  TestObject(std::string _addr, unsigned _count, std::string _data, size_t _align, MemKind _kind, std::string _name, std::string _type) :
      count(_count), align(_align), kind(_kind), name(_name), type(_type) {

    std::stringstream ss(_addr);
    ss >> std::hex >> addr;
    addr = boost::endian::endian_reverse(addr);
    fromDataString(data, _data);
  }

  uintptr_t addr;
  unsigned count;
  std::vector<unsigned char> data;
  size_t align;
  MemKind kind;
  std::string name;
  std::string type;
};

class TestCase {
public:

  TestCase() : arg_c(0),
               lazy_alloc_count(0),
               lazy_string_length(0),
               max_lazy_depth(0),
               max_loop_forks(0),
               max_loop_iter(0),
               term_reason(TerminateReason::Invalid),
               test_id(UINT_MAX),
               trace_type(TraceType::invalid) {}
  bool is_ready() { return test_id != UINT_MAX; }

  int arg_c;
  std::string arg_v;
  std::string module_name;
  std::string file_name;
  std::string entry_fn;
  std::string klee_version;
  unsigned lazy_alloc_count;
  unsigned lazy_string_length;
  unsigned max_lazy_depth;
  unsigned max_loop_forks;
  unsigned max_loop_iter;
  std::string message;
  std::string path_condition_vars;
  TerminateReason term_reason;
  unsigned test_id;
  sys_clock::time_point start;
  sys_clock::time_point stop;
  TraceType trace_type;
  UnconstraintFlagsT unconstraintFlags;
  std::vector<uint64_t> arguments;
  std::vector<unsigned> trace;
  std::vector<TestObject> objects;
  std::vector<unsigned char> stdin_buffer;
  std::vector<int> fps_produced;

  bool is_main() const {
    for (const auto &obj : objects) {
      // this object is only inserted by unconstrained ex from main
      if (obj.name == "#program_name") return true;
    }
    return false;
  }

};

}

#endif
