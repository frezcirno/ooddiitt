
#ifndef KLEE_COMMONUTIL_H
#define KLEE_COMMONUTIL_H

#include <chrono>
typedef std::chrono::system_clock sys_clock;

namespace klee {

enum class StateStatus {
  Invalid,
  Pending,
  Completed,
  Faulted,
  TerminateEarly,
  TerminateError,
  Decimated,
  TerminateDiscard,
  Snapshot
};

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

enum class TraceType {
  undefined,
  none,
  bblocks,
  assembly,
  statements
};

sys_clock::time_point to_time_point(const std::string &str);
std::string to_string(const sys_clock::time_point &tp);
std::string currentISO8601TimeUTC();

};

#endif // KLEE_COMMONUTIL_H

