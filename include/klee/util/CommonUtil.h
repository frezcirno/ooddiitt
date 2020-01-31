
#ifndef KLEE_COMMONUTIL_H
#define KLEE_COMMONUTIL_H

#include <chrono>
#include <llvm/IR/Type.h>
#include <llvm/ADT/Hashing.h>

typedef std::chrono::system_clock sys_clock;

#define countof(a) (sizeof(a)/ sizeof(a[0]))

namespace llvm {
  class Value;
}

namespace klee {

enum class TerminateReason {
  Abort,
  Assert,
  Exec,
  External,
  Free,
  Model,
  Overflow,
  Ptr,
  ReadOnly,
  ReportError,
  User,
  Unhandled
};

std::string to_string(TerminateReason s);

enum class StateStatus {
  Invalid,
  Pending,
  Completed,
  Error,
  MemFaulted,
  Incomplete,
  Decimated,
  Discarded,
  Snapshot
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
  lazy
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

std::string to_string(MarkScope m);
std::string to_string(const llvm::Type *type);

void filterHandledFunctions(std::set<const llvm::Value*> &fns);
void filterHandledGlobals(std::set<const llvm::Value*> &gbs);

sys_clock::time_point to_time_point(const std::string &str);
std::string to_string(const sys_clock::time_point &tp);
std::string currentISO8601TimeUTC();

class HashAccumulator {
  uint64_t hash;
public:
  HashAccumulator() : hash(0x89f88ec5e917b55e) {}
  void add(uint64_t val) { hash = llvm::hashing::detail::hash_16_bytes(hash, val); }
  void add(double val)   { assert(sizeof(uint64_t) == sizeof(double)); hash = llvm::hashing::detail::hash_16_bytes(hash, (uint64_t) val); }
  void add(const std::string &str);
  uint64_t get() const { return hash; }
};

#ifdef _DEBUG
bool EnableMemDebuggingChecks();
void ShowMemStats();
#endif // _DEBUG

} // namespace klee

#endif // KLEE_COMMONUTIL_H

