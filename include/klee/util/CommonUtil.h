
#ifndef KLEE_COMMONUTIL_H
#define KLEE_COMMONUTIL_H

#include <chrono>
#include <bitset>
#include <llvm/IR/Type.h>
#include <llvm/ADT/Hashing.h>
#include <llvm/Support/raw_ostream.h>

typedef std::chrono::system_clock sys_clock;

#define countof(a) (sizeof(a)/ sizeof(a[0]))

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

class UnconstraintFlagsT : public std::bitset<8> {

public:
  UnconstraintFlagsT() = default;
  explicit UnconstraintFlagsT(std::string s) : std::bitset<8>(s) { }
  bool isStubCallees() const          { return test(UNCONSTRAIN_STUB_FLAG); }
  bool isUnconstrainGlobals() const   { return test(UNCONSTRAIN_GLOBAL_FLAG); }

  void setStubCallees(bool b = true)          { set(UNCONSTRAIN_STUB_FLAG, b); }
  void setUnconstrainGlobals(bool b = true)   { set(UNCONSTRAIN_GLOBAL_FLAG, b); }
};

typedef std::pair<const char*,unsigned> TraceEntryT;
typedef std::deque<TraceEntryT> TraceDequeT;
std::string to_string(const TraceEntryT &entry);

std::string to_string(UnconstraintFlagsT flags);
std::string to_string(MarkScope m);
std::string to_string(const llvm::Type *type);

void fromDataString(std::vector<unsigned char> &data, const std::string &str);
std::string toDataString(const std::vector<unsigned char> &data, unsigned max = UINT32_MAX);

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

