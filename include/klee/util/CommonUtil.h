//===-----------------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#pragma once

#include <chrono>
#include <bitset>
#include <list>
#include <string>
#include <set>
#include <llvm/IR/Type.h>
#include <llvm/ADT/Hashing.h>
#include <llvm/Support/raw_ostream.h>

typedef std::chrono::system_clock sys_clock;

// if not already defined, define some common macros
#ifndef countof
#define countof(a) (sizeof(a)/ sizeof(a[0]))
#endif

#ifndef __noop
#define __noop()  asm("nop")
#endif

#ifndef UNUSED
#define UNUSED(x) {(void)(x);}
#endif

//-------------------------------------------------------
// because the usual set containment idium is so unreadable.

namespace std {

template <class TInputIterator, class T> inline bool contains(TInputIterator first, TInputIterator last, const T &value) {
  return std::find(first, last, value) != last;
}

template <class TContainer, class T> inline bool contains(const TContainer &container, const T &value) {
  return contains(std::begin(container), std::end(container), value);
}

template <class T> inline bool contains(const std::set<T> &container, const T &value) {
  return container.find(value) != container.end();
}

template <typename T> struct set_ex : std::set<T> {
  using std::set<T>::set;
  bool contains(const T &value) const { return (this->find(value) != this->end()); }
};


} // end std namespace
//-------------------------------------------------------

namespace llvm {
  class Value;

enum class RawOStreamOperator {
  base_flush,
  base_endl,
  base_endf
};

extern RawOStreamOperator oflush;
extern RawOStreamOperator oendl;
extern RawOStreamOperator oendf;

llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const RawOStreamOperator &op);

} // end namespace llvm

namespace klee {

enum class TerminateReason {
  Return,
  Exit,
  Abort,
  Invalid,
  Assert,
  ExternFn,
  InvalidFree,
  MemFault,
  ROFault,
  InvalidCall,
  UnhandledInst,
  InternalFault,
  InvalidAssume,
  Overflow,
  Snapshot,
  Timeout,
  FailedLibcInit,
};

std::string to_string(TerminateReason s);
inline bool is_valid(TerminateReason s) { return (s < TerminateReason::Invalid); }

enum class StateStatus {
  Waiting,
  Completed,
  Decimated,
  Discarded
};

std::string to_string(StateStatus s);

enum class MemKind {
  invalid,
  external,
  global,
  param,
  alloca_l,
  heap,
  output,
  lazy,
  va_arg
};

std::string to_string(MemKind k);

enum class TraceType {
  invalid,
  none,
  bblocks,
  assembly,
  statements,
  calls
};

std::string to_string(TraceType t);

enum class MarkScope {
  invalid,
  none,
  module,
  all
};

#define UNCONSTRAIN_GLOBAL_FLAG (0)
#define UNCONSTRAIN_STUB_FLAG   (2)
#define UNCONSTRAIN_EXTERN_FLAG (3)

class UnconstraintFlagsT : public std::bitset<8> {

public:
  UnconstraintFlagsT() = default;
  explicit UnconstraintFlagsT(std::string s) : std::bitset<8>(s) { }
  bool isStubCallees() const          { return test(UNCONSTRAIN_STUB_FLAG); }
  bool isUnconstrainGlobals() const   { return test(UNCONSTRAIN_GLOBAL_FLAG); }
  bool isUnconstrainExterns() const   { return test(UNCONSTRAIN_EXTERN_FLAG); }

  void setStubCallees(bool b = true)          { set(UNCONSTRAIN_STUB_FLAG, b); }
  void setUnconstrainGlobals(bool b = true)   { set(UNCONSTRAIN_GLOBAL_FLAG, b); }
  void setUnconstrainExterns(bool b = true)   { set(UNCONSTRAIN_EXTERN_FLAG, b); }
};

typedef std::pair<const char*,unsigned> TraceEntryT;
typedef std::deque<TraceEntryT> TraceDequeT;
std::string to_string(const TraceEntryT &entry);

std::string to_string(UnconstraintFlagsT flags);
std::string to_string(MarkScope m);
std::string to_string(const llvm::Type *type);

void fromDataString(std::vector<unsigned char> &data, const std::string &str);
std::string toDataString(const std::vector<unsigned char> &data, unsigned max = UINT32_MAX);
void expandTestFiles(const std::string &file, const std::string &dir, const std::string &prefix, std::deque<std::string> &files);

void filterHandledFunctions(std::set<const llvm::Value*> &fns);
void filterHandledGlobals(std::set<const llvm::Value*> &gbs);

sys_clock::time_point to_time_point(const std::string &str);
std::string to_string(const sys_clock::time_point &tp);
std::string currentISO8601TimeUTC();
void show_args(int argc, char *argv[]);

class HashAccumulator {
  uint64_t hash;
public:
  HashAccumulator() : hash(0x89f88ec5e917b55e) {}
  void add(uint64_t val) {
    hash = llvm::hashing::detail::hash_16_bytes(hash, val);
  }
  void add(double val) {
    assert(sizeof(uint64_t) == sizeof(double));
    hash = llvm::hashing::detail::hash_16_bytes(hash, (uint64_t) val);
  }
  void add(const std::string &str);
  uint64_t get() const { return hash; }
};

#ifdef _DEBUG
bool EnableMemDebuggingChecks();
void ShowMemStats();
#endif // _DEBUG

} // namespace klee


