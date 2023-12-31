//===-----------------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <string>
#include <sstream>
#include <iomanip>
#include <set>
#include <zconf.h>

#include <boost/filesystem.hpp>
#include <boost/algorithm/string.hpp>

#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/CommandLine.h"

#include "klee/util/CommonUtil.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "../Core/SpecialFunctionHandler.h"
#include "../Core/SystemModel.h"


namespace llvm {
RawOStreamOperator oflush = RawOStreamOperator::base_flush;
RawOStreamOperator oendl = RawOStreamOperator::base_endl;
RawOStreamOperator oendf = RawOStreamOperator::base_endf;

llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const RawOStreamOperator &op) {
  switch(op) {
    case RawOStreamOperator::base_endl:
      os << '\n';
      break;

    case RawOStreamOperator::base_flush:
      os.flush();
      break;

    case RawOStreamOperator::base_endf:
      os << '\n';
      os.flush();
      break;

    default:
      assert("invalid rawstream operator");
  }
  return os;
}

};

using namespace std;
namespace fs=boost::filesystem;

namespace klee {

static string st_cmdline;
static string st_err_context;

void parseCmdLineArgs(int argc, char *argv[], bool show) {
  llvm::cl::SetVersionPrinter(printVersion);
  llvm::cl::ParseCommandLineOptions(argc, argv, " brt-klee\n");

  SetupStackTraceSignalHandler(argc, argv);
  if (show) {
    llvm::outs() << '#' << st_cmdline << '\n';
  }
}

void PrintStackTraceSignalHandler(void *) {
  if (!st_cmdline.empty()) {
    fprintf(stderr, "cmdline: %s\n", st_cmdline.c_str());
  }
  if (!st_err_context.empty()) {
    fprintf(stderr, "context: %s\n", st_err_context.c_str());
  }
  llvm::sys::PrintStackTrace(stderr);
}

void SetupStackTraceSignalHandler(int argc, char *argv[]) {

  st_cmdline.clear();
  st_err_context.clear();
  ostringstream ss;
  for (int idx = 0; idx < argc; ++idx, ++argv) {
    if (idx > 0) ss << ' ';
    ss << *argv;
  }
  st_cmdline = ss.str();
  llvm::sys::AddSignalHandler(PrintStackTraceSignalHandler, nullptr);
}

void SetStackTraceContext(const string &str) {
  st_err_context = str;
}

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

void fromDataString(vector<unsigned char> &data, const string &str) {

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

string toDataString(const vector<unsigned char> &data, unsigned max) {

  unsigned counter = 0;
  ostringstream bytes;
  for (auto itrData = data.begin(), endData = data.end(); (itrData != endData) && (counter++ < max); ++itrData) {

    unsigned char hi = (unsigned char) (*itrData >> 4);
    unsigned char low = (unsigned char) (*itrData & 0x0F);
    hi = (unsigned char) ((hi > 9) ? ('A' + (hi - 10)) : ('0' + hi));
    low = (unsigned char) ((low > 9) ? ('A' + (low - 10)) : ('0' + low));
    bytes << hi << low;
  }
  return bytes.str();
}

std::string to_string(TerminateReason s) {
  static const char *strings[] = {"return", "exit", "abort", "invalid", "assert", "extern_fn", "invalid_free", "mem_fault",
                                  "readonly_fault", "invalid_call", "unhandled_instuction", "internal_fault",
                                  "invalid_assume", "overflow", "snapshot", "timeout", "failed_libc_init" };
  if ((unsigned) s >= countof(strings))
    return "";
  return strings[(unsigned) s];
}

std::string to_string(StateStatus s) {
  static const char *strings[] = {"waiting", "completed", "decimated", "discarded"};
  if ((unsigned) s >= countof(strings))
    return "";
  return strings[(unsigned) s];
}

std::string to_string(MemKind k) {
  static const char *strings[] = {"invalid", "external", "global", "param", "alloca", "heap", "output", "lazy", "va_arg"};
  if ((unsigned) k >= countof(strings))
    return "";
  return strings[(unsigned) k];
}

std::string to_string(TraceType t) {
  static const char *strings[] = {"invalid", "none", "bblocks", "assembly", "statements", "calls"};
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

std::string to_string(UnconstraintFlagsT flags) {

  const static std::vector< std::pair<unsigned,const std::string> > flag2name =  {
      std::make_pair(UNCONSTRAIN_GLOBAL_FLAG, "globals"),
      std::make_pair(UNCONSTRAIN_STUB_FLAG, "stubs"),
      std::make_pair(UNCONSTRAIN_EXTERN_FLAG, "externs")
  };

  std::ostringstream ss;
  ss << "inputs";
  for (auto &p: flag2name) {
    if (flags.test(p.first)) ss << ',' << p.second;
  }
  return ss.str();
}

string to_string(const TraceEntryT &entry) {

  ostringstream ss;
  if (entry.first != nullptr) {
    ss << entry.first << ':';
  }
  ss << entry.second;
  return ss.str();
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

void expandTestFiles(const string &file, const string &dir, const string &prefix, deque<string> &files) {

  // if tests are not specified, then default to all tests in the output directory
  deque<string> worklist;
  worklist.push_back(file);

  while (!worklist.empty()) {
    string str = worklist.front();
    worklist.pop_front();
    fs::path entry(str);
    boost::system::error_code ec;
    fs::file_status s = fs::status(entry, ec);
    if (fs::is_regular_file(s)) {
      files.push_back(str);
    } else if (fs::is_directory(s)) {
      for (fs::directory_iterator itr{entry}, end{}; itr != end; ++itr) {
        // add regular files of the form test*.json
        fs::path pfile(itr->path());
        if (fs::is_regular_file(pfile) && (pfile.extension().string() == ".json") &&
            (boost::starts_with(pfile.filename().string(), prefix))) {

          files.push_back(pfile.string());
        }
      }
    } else if (entry.parent_path().empty()) {
      // only filename given, try the output directory
      string new_str = (dir / entry).string();
      if (new_str != str) worklist.push_back(new_str);
    } else {
      klee_error("Test file not found: %s", str.c_str());
    }
  }
}

extern RNG theRNG;

BagOfNumbers::BagOfNumbers(unsigned size) {
  for (unsigned idx = 0; idx < size; ++idx) {
    numbers.push_back(idx);
  }
}

unsigned BagOfNumbers::draw() {

  unsigned result = 0;
  if (!numbers.empty()) {
    unsigned idx = theRNG.getInt32() % numbers.size();
    result = numbers.at(idx);
    numbers.erase(numbers.begin() + idx);
  }
  return result;
}

#ifdef _DEBUG

#include <gperftools/tcmalloc.h>
#include <gperftools/malloc_hook.h>
#include <gperftools/malloc_extension_c.h>
#include <malloc.h>
#include <string.h>

#define MEM_ALLOCD  (0xCD)
#define MEM_FREEDD  (0xCD)

int64_t allocation_counter;
size_t max_allocation_size;

static void DebugNewHook(const void *ptr, size_t size) {

  allocation_counter += 1;
  max_allocation_size = std::max(size, max_allocation_size);

  //  memset((void*) ptr, MEM_ALLOCD, size);
}

static void DebugDeleteHook(const void *ptr) {

  allocation_counter -= 1;
//  if (size_t size = tc_malloc_size((void*) ptr) > 0) {
//    memset((void*) ptr, MEM_FREEDD, size);
//  }
}

void DisableMemDebuggingChecks() {

  MallocHook::RemoveNewHook(DebugNewHook);
  MallocHook::RemoveDeleteHook(DebugDeleteHook);
}

bool EnableMemDebuggingChecks() {

//  atexit(DisableMemDebuggingChecks);
//  return (MallocHook::AddNewHook(DebugNewHook) && MallocHook::AddDeleteHook(DebugDeleteHook));
  return true;
}

void ShowMemStats() {
  llvm::errs() << "Allocation Counter: " << allocation_counter << '\n';
}


#endif // _DEBUG

};

