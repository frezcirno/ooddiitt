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

  static void fromDataString(std::vector<unsigned char> &data, const std::string &str) {

    assert(str.size() % 2 == 0);
    data.clear();
    data.reserve(str.size() / 2);

    unsigned char val = 0;
    unsigned counter = 0;
    for (const auto &ch : str) {
      unsigned char nibble = 0;
      if (isdigit(ch)) nibble = ch - '0';
      else if (ch >= 'A' && ch <= 'F') nibble = ch - 'A' + 10;
      if (counter++ % 2 == 0) {
        val = nibble;
      } else {
        val = (val << 4) | nibble;
        data.push_back(val);
      }
    }
  }

};

class TestCase {
public:

  TestCase() : arg_c(0),
               lazy_alloc_count(0),
               lazy_string_length(0),
               max_lazy_depth(0),
               max_loop_forks(0),
               max_loop_iter(0),
               status(StateStatus::Invalid),
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
  StateStatus status;
  unsigned test_id;
  sys_clock::time_point start;
  sys_clock::time_point stop;
  TraceType trace_type;
  std::vector<uint64_t> arguments;
  std::vector<unsigned> trace;
  std::vector<TestObject> objects;
  std::vector<unsigned char> stdin_buffer;
};

}

#endif
