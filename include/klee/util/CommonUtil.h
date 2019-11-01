
#ifndef KLEE_COMMONUTIL_H
#define KLEE_COMMONUTIL_H

#include <chrono>
typedef std::chrono::system_clock sys_clock;

namespace klee {

enum StateStatus {
  Pending,
  Completed,
  Faulted,
  TerminateEarly,
  TerminateError,
  Decimated,
  TerminateDiscard,
  Invalid
};

enum MemKind {
  invalid,
  fixed,
  global,
  param,
  alloca_l,
  heap,
  output,
  lazy
};

sys_clock::time_point to_time_point(const std::string &str);
std::string to_string(const sys_clock::time_point &tp);
std::string currentISO8601TimeUTC();

};

#endif // KLEE_COMMONUTIL_H

