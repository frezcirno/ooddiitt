
#ifndef KLEE_COMMONUTIL_H
#define KLEE_COMMONUTIL_H

#include <chrono>
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

inline std::string to_string(TerminateReason s) {
  static const char *strings[] = {"abort", "assert", "exec", "external", "free", "model", "overflow",
                                  "ptr", "readonly", "report_error", "user", "unhandled"};
  if ((unsigned) s >= countof(strings))
    return "";
  return strings[(unsigned) s];
}

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

inline std::string to_string(StateStatus s) {
  static const char *strings[] = {"invalid", "pending", "completed", "error", "faulted",
                                  "incomplete", "decimated", "discarded", "snapshot"};
  if ((unsigned) s >= countof(strings))
    return "";
  return strings[(unsigned) s];
}

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

inline std::string to_string(MemKind k) {
  static const char *strings[] = {"invalid", "external", "global", "param", "alloca", "heap", "output", "lazy"};
  if ((unsigned) k >= countof(strings))
    return "";
  return strings[(unsigned) k];
}

enum class TraceType {
  invalid,
  none,
  bblocks,
  assembly,
  statements
};

inline std::string to_string(TraceType t) {
  static const char *strings[] = {"invalid", "none", "bblocks", "assembly", "statements"};
  if ((unsigned) t >= countof(strings))
    return "";
  return strings[(unsigned) t];
}

enum class MarkScope {
  invalid,
  none,
  module,
  all
};

inline std::string to_string(MarkScope m) {
  static const char *strings[] = {"invalid", "none", "module", "all"};
  if ((unsigned) m >= countof(strings))
    return "";
  return strings[(unsigned) m];
}


void filterHandledFunctions(std::set<const llvm::Value*> &fns);
void filterHandledGlobals(std::set<const llvm::Value*> &gbs);

sys_clock::time_point to_time_point(const std::string &str);
std::string to_string(const sys_clock::time_point &tp);
std::string currentISO8601TimeUTC();


#ifdef _DEBUG
bool EnableMemDebuggingChecks();
#endif // _DEBUG

} // namespace klee

#endif // KLEE_COMMONUTIL_H

