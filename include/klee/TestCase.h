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

typedef std::chrono::system_clock sys_clock;

namespace klee {

class TestObject {
public:
  TestObject(std::string _addr, unsigned _count, std::string _data, std::string _kind, std::string _name, std::string _type) :
    count(_count), name(_name), type(_type) {

    std::stringstream ss(_addr);
    ss >> std::hex >> addr;
    addr = boost::endian::endian_reverse(addr);
    fromDataString(data, _data);
    kind = fromKindString(_kind);
  }

  uintptr_t addr;
  unsigned count;
  std::vector<unsigned char> data;
  int kind;
  std::string name;
  std::string type;

  void fromDataString(std::vector<unsigned char> &data, const std::string &str) const {

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

  int fromKindString(const std::string &str) const {
    static const std::vector<std::string> kindStrings = {"invalid", "fixed", "global", "param", "alloca", "heap", "output", "lazy"};
    auto itr = std::find(kindStrings.begin(), kindStrings.end(), str);
    if (itr != kindStrings.end()) return std::distance(kindStrings.begin(), itr);
    return 0;
  }

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
  int status;
  unsigned test_id;
  sys_clock::time_point start;
  sys_clock::time_point stop;
  std::deque<unsigned> trace;
  std::deque<TestObject> objects;

  static int fromStatusString(const std::string &str)  {
    static const std::vector<std::string> statusStrings = { "pending",  "completed",  "faulted",  "early", "error", "decimate",  "discard" };
    auto itr = std::find(statusStrings.begin(), statusStrings.end(), str);
    if (itr != statusStrings.end()) return std::distance(statusStrings.begin(), itr);
    return statusStrings.size();
  }

};

}

#endif
