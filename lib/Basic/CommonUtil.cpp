

#include <string>
#include <sstream>
#include <iomanip>
#include <set>
#include "klee/util/CommonUtil.h"
#include "../Core/SpecialFunctionHandler.h"
#include "../Core/SystemModel.h"
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>

using namespace std;

namespace klee {

sys_clock::time_point to_time_point(const string &str) {

  tm _tm;
  stringstream ss(str);
  ss >> get_time(&_tm, "\"%FT%TZ\"");
  return sys_clock::from_time_t(mktime(&_tm));
}

string to_string(const sys_clock::time_point &tp) {

  auto itt = sys_clock::to_time_t(tp);
  ostringstream ss;
  ss << put_time(gmtime(&itt), "%FT%TZ");
  return ss.str();
}

string currentISO8601TimeUTC() {
  return to_string(sys_clock::now());
}


void filterHandledFunctions(set<const llvm::Value*> &fns) {

  SpecialFunctionHandler::filterHandledFunctions(fns);
  SystemModel::filterHandledFunctions(fns);
}

void filterHandledGlobals(set<const llvm::Value*> &gbs) {

  SpecialFunctionHandler::filterHandledGlobals(gbs);
  SystemModel::filterHandledGlobals(gbs);
}

std::string to_string(TerminateReason s) {
  static const char *strings[] = {"abort", "assert", "exec", "external", "free", "model", "overflow",
                                  "ptr", "readonly", "report_error", "user", "unhandled"};
  if ((unsigned) s >= countof(strings))
    return "";
  return strings[(unsigned) s];
}

std::string to_string(StateStatus s) {
  static const char *strings[] = {"invalid", "pending", "completed", "error", "faulted",
                                  "incomplete", "decimated", "discarded", "snapshot"};
  if ((unsigned) s >= countof(strings))
    return "";
  return strings[(unsigned) s];
}

std::string to_string(MemKind k) {
  static const char *strings[] = {"invalid", "external", "global", "param", "alloca", "heap", "output", "lazy"};
  if ((unsigned) k >= countof(strings))
    return "";
  return strings[(unsigned) k];
}

std::string to_string(TraceType t) {
  static const char *strings[] = {"invalid", "none", "bblocks", "assembly", "statements"};
  if ((unsigned) t >= countof(strings))
    return "";
  return strings[(unsigned) t];
}

std::string to_string(MarkScope m) {
  static const char *strings[] = {"invalid", "none", "module", "all"};
  if ((unsigned) m >= countof(strings))
    return "";
  return strings[(unsigned) m];
}

std::string to_string(const llvm::Type *type) {
  if (type == nullptr) return "nil";
  std::string str;
  llvm::raw_string_ostream rss(str);
  type->print(rss);
  return rss.str();
}

void HashAccumulator::add(const std::string &str) {

  if (str.empty()) {
    add((uint64_t) 0xf7614045);
  } else {

    // treat each succeeding chucks of the string as a number
    unsigned idx = 0, end = str.length();
    while (idx < end) {
      if (end - idx > sizeof(uint64_t)) {
        const char *bytes = str.substr(idx, sizeof(uint64_t)).c_str();
        add(*((uint64_t *) bytes));
        idx += sizeof(uint64_t);
      } else {
        // remaining bytes will not fit into a uint64_t.
        // this alternate buffer insures bytes after remaining tail of string are the same
        unsigned char buffer[sizeof(uint64_t)];
        memset(buffer, 0x1e, sizeof(buffer));
        unsigned remaining = end - idx;
        const char *bytes = str.substr(idx, remaining).c_str();
        memcpy(buffer, bytes, remaining);
        add(*((uint64_t *) buffer));
        idx += remaining;
      }
    }
  }
}


#ifdef _DEBUG

#include <gperftools/tcmalloc.h>
#include <gperftools/malloc_hook.h>
#include <malloc.h>
#include <string.h>

#define MEM_ALLOCD  (0xCD)
#define MEM_FREEDD  (0xCD)

int64_t allocation_counter;

static void DebugNewHook(const void *ptr, size_t size) {

  allocation_counter += 1;
//  memset((void*) ptr, MEM_ALLOCD, size);
}

static void DebugDeleteHook(const void *ptr) {

  allocation_counter -= 1;
//  if (size_t size = tc_malloc_size((void*) ptr) > 0) {
//    memset((void*) ptr, MEM_FREEDD, size);
//  }
}

static void DisableMemDebuggingChecks() {

  MallocHook::RemoveNewHook(DebugNewHook);
  MallocHook::RemoveDeleteHook(DebugDeleteHook);
}

bool EnableMemDebuggingChecks() {

  atexit(DisableMemDebuggingChecks);
  return (MallocHook::AddNewHook(DebugNewHook) && MallocHook::AddDeleteHook(DebugDeleteHook));
}

void ShowMemStats() {
  llvm::errs() << "Allocation Counter: " << allocation_counter << '\n';
}


#endif // _DEBUG

};

