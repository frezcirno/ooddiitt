

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

#ifdef _DEBUG

#include <gperftools/tcmalloc.h>
#include <gperftools/malloc_hook.h>
#include <malloc.h>
#include <string.h>

#define MEM_ALLOCD  (0xCD)
#define MEM_FREEDD  (0xCD)

static void DebugNewHook(const void *ptr, size_t size) {

  memset((void*) ptr, MEM_ALLOCD, size);
}

static void DebugDeleteHook(const void *ptr) {

  if (size_t size = tc_malloc_size((void*) ptr) > 0) {
    memset((void*) ptr, MEM_FREEDD, size);
  }
}

static void DisableMemDebuggingChecks() {

  MallocHook::RemoveNewHook(DebugNewHook);
  MallocHook::RemoveDeleteHook(DebugDeleteHook);
}

bool EnableMemDebuggingChecks() {

  atexit(DisableMemDebuggingChecks);
//  return (MallocHook::AddNewHook(DebugNewHook) && MallocHook::AddDeleteHook(DebugDeleteHook));
  return true;
}

#endif // _DEBUG

};

