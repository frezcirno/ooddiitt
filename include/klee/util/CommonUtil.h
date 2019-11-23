
#ifndef KLEE_COMMONUTIL_H
#define KLEE_COMMONUTIL_H

#include <chrono>
typedef std::chrono::system_clock sys_clock;

#define countof(a) (sizeof(a)/ sizeof(a[0]))

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
  static const char* strings[] = {"abort", "assert", "exec", "external", "free", "model", "overflow",
                                  "ptr", "readonly", "report_error", "user", "unhandled" };
  unsigned idx = (unsigned) s;
  if (idx >= countof(strings)) return "";
  return strings[idx];
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
  static const char* strings[] = {"invalid", "pending", "completed", "error", "faulted",
                                  "incomplete", "decimated", "discarded", "snapshot"};
  unsigned idx = (unsigned) s;
  if (idx >= countof(strings)) return "";
  return strings[idx];
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
  static const char* strings[] = {"invalid", "external", "global", "param", "alloca", "heap", "output", "lazy"};
  unsigned idx = (unsigned) k;
  if (idx >= countof(strings)) return "";
  return strings[idx];
}

enum class TraceType {
  invalid,
  none,
  bblocks,
  assembly,
  statements
};

inline std::string to_string(TraceType t) {
  static const char* strings[] = {"invalid", "none", "bblocks", "assembly", "statements" };
  unsigned idx = (unsigned) t;
  if (idx >= countof(strings)) return "";
  return strings[idx];
}


sys_clock::time_point to_time_point(const std::string &str);
std::string to_string(const sys_clock::time_point &tp);
std::string currentISO8601TimeUTC();

};

#endif // KLEE_COMMONUTIL_H

