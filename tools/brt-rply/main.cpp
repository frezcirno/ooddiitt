//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"
#include "klee/Interpreter.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/Timer.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/system_error.h"
#endif

#include <string>
#include <iomanip>
#include <iterator>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include <klee/Internal/Support/ModuleUtil.h>
#include "json/json.h"
#include "klee/TestCase.h"
#include "klee/util/CommonUtil.h"


//#define DO_HEAP_PROFILE 1

#ifdef DO_HEAP_PROFILE
#include <gperftools/tcmalloc.h>
#include <gperftools/heap-profiler.h>
#include <gperftools/heap-checker.h>
#endif // DO_HEAP_PROFILE

using namespace llvm;
using namespace klee;
using namespace std;
namespace fs=boost::filesystem;

namespace {
  cl::list<string> ReplayTests(cl::desc("<test case to replay>"), cl::Positional, cl::ZeroOrMore);
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
  cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));
  cl::opt<bool> CheckTrace("check-trace", cl::desc("compare executed trace to test case"), cl::init(false));
  cl::opt<bool> UpdateTrace("update-trace", cl::desc("update test case trace, if differs from replay"));
  cl::opt<bool> ShowOutput("show-output", cl::desc("display replay's stdout and stderr"));
  cl::opt<unsigned> ShowFnFreq("show-fn-freq", cl::desc("display function's basic block frequency"));
  cl::opt<bool> Verbose("verbose", cl::desc("Display additional information about replay"));
  cl::opt<string> ModuleName("module", cl::desc("override module specified by test case"));
  cl::opt<string> Prefix("prefix", cl::desc("prefix for loaded test cases"), cl::init("test"));
  cl::opt<TraceType> TraceT("trace",
                            cl::desc("Choose the type of trace (default=marked basic blocks"),
                            cl::values(clEnumValN(TraceType::none, "none", "do not trace execution"),
                                       clEnumValN(TraceType::bblocks, "bblk", "trace execution by basic block"),
                                       clEnumValN(TraceType::statements, "stmt", "trace execution by source statement"),
                                       clEnumValN(TraceType::assembly, "assm", "trace execution by assembly line"),
                                       clEnumValN(TraceType::calls, "calls", "trace execution by function call/return"),
                                       clEnumValEnd),
                            cl::init(TraceType::invalid));

}

/***/

class ReplayKleeHandler : public InterpreterHandler {
private:
  string indentation;
  vector<ExecutionState*> &results;

public:
  ReplayKleeHandler(vector<ExecutionState*> &_results, const string &_md_name);
  ~ReplayKleeHandler() override = default;

  void processTestCase(ExecutionState  &state) override;
};

ReplayKleeHandler::ReplayKleeHandler(vector<ExecutionState*> &_results, const string &_md_name)
  : InterpreterHandler(Output, _md_name),
    indentation(""),
    results(_results) {

  assert(results.empty());

  if (IndentJson) indentation = "  ";
}

void ReplayKleeHandler::processTestCase(ExecutionState &state) {

  results.push_back(new ExecutionState(state));
}

//===----------------------------------------------------------------------===//
// main Driver function
//

static void parseArguments(int argc, char **argv) {
  cl::SetVersionPrinter(klee::printVersion);
  cl::ParseCommandLineOptions(argc, argv, " klee\n");
}

static Interpreter *theInterpreter = nullptr;
static bool interrupted = false;

// Pulled out so it can be easily called from a debugger.
extern "C"
void halt_execution() {
  theInterpreter->setHaltExecution(true);
}

extern "C"
void stop_forking() {
  theInterpreter->setInhibitForking(true);
}


static int exit_code = 0;

static void interrupt_handle() {

  if (theInterpreter == nullptr) {
    llvm::errs() << "KLEE: ctrl-c received without interpreter\n";
  } else {
    if (!interrupted) {
      llvm::errs() << "KLEE: ctrl-c detected, requesting interpreter to halt.\n";
      halt_execution();
      sys::SetInterruptFunction(interrupt_handle);
      exit_code = 3;
    } else {
      llvm::errs() << "KLEE: 2nd ctrl-c detected, exiting.\n";
      exit(4);
    }
    interrupted = true;
  }
}

void load_test_case(Json::Value &root, TestCase &test) {

  // complete test case from json structure
  test.arg_c = root["argC"].asInt();
  test.arg_v = root["argV"].asString();

  test.module_name = root["module"].asString();
  test.file_name = root["file"].asString();
  test.entry_fn = root["entryFn"].asString();
  test.klee_version = root["kleeRevision"].asString();
  test.lazy_alloc_count = root["lazyAllocationCount"].asUInt();
  test.lazy_string_length = root["lazyStringLength"].asUInt();
  test.max_lazy_depth = root["maxLazyDepth"].asUInt();
  test.max_loop_forks = root["maxLoopForks"].asUInt();
  test.max_loop_iter = root["maxLoopIteration"].asUInt();
  test.message = root["message"].asString();
  test.path_condition_vars = root["pathConditionVars"].asString();
  test.status = (StateStatus) root["status"].asUInt();
  test.test_id = root["testID"].asUInt();
  test.start = to_time_point(root["timeStarted"].asString());
  test.stop = to_time_point(root["timeStopped"].asString());
  fromDataString(test.stdin_buffer, root["stdin"].asString());

  Json::Value &args = root["arguments"];
  if (args.isArray()) {
    test.arguments.reserve(args.size());
    for (unsigned idx = 0, end = args.size(); idx < end; ++idx) {
      string value = args[idx].asString();
      vector<unsigned char> bytes;
      fromDataString(bytes, value);
      uint64_t v = 0;
      switch (bytes.size()) {
      case 1:
        v = *((uint8_t*) bytes.data());
        break;
      case 2:
        v = *((uint16_t*) bytes.data());
        break;
      case 4:
        v = *((uint32_t*) bytes.data());
        break;
      case 8:
        v = *((uint64_t*) bytes.data());
        break;
      default:
        assert(false && "unsupported data width");
        break;
      }
      test.arguments.push_back(v);
    }
  }

  test.trace_type = (TraceType) root["traceType"].asUInt();
  Json::Value &trace = root["trace"];
  if (trace.isArray()) {
    test.trace.reserve(trace.size());
    for (unsigned idx = 0, end = trace.size(); idx < end; ++idx) {
      test.trace.push_back(trace[idx].asUInt());
    }
  }

  Json::Value &objs = root["objects"];
  if (objs.isArray()) {
    test.objects.reserve(objs.size());
    for (unsigned idx = 0, end = objs.size(); idx < end; ++idx) {
      Json::Value &obj = objs[idx];
      string addr = obj["addr"].asString();
      unsigned count = obj["count"].asUInt();
      string data = obj["data"].asString();
      size_t align = obj["align"].asInt64();
      MemKind kind = (MemKind) obj["kind"].asUInt();
      string name = obj["name"].asString();
      string type = obj["type"].asString();
      test.objects.emplace_back(TestObject(addr, count, data, align, kind, name, type));
    }
  }
}

bool update_test_case(const string &fname, Json::Value &root, const deque<unsigned> &trace) {

  // add the new trace as a new entity
  Json::Value &rtrace = root["replyTrace"] = Json::arrayValue;
  for (auto entry : trace) {
    rtrace.append(entry);
  }

  ofstream info;
  info.open(fname);
  if (info.is_open()) {

    string indentation;
    if (IndentJson)
      indentation = "  ";

    Json::StreamWriterBuilder builder;
    builder["commentStyle"] = "None";
    builder["indentation"] = indentation;
    unique_ptr<Json::StreamWriter> writer(builder.newStreamWriter());
    writer->write(root, &info);
    info << endl;
  } else {
    errs() << "error writing test case\n";
    return false;
  }
  return true;
}

enum class TraceCompareResult { ok, truncated, differs };

TraceCompareResult compare_traces(const vector<unsigned> &t_trace, const deque<unsigned> &s_trace) {

  if (boost::starts_with(t_trace, s_trace)) {
    if (t_trace.size() == s_trace.size()) {
      return TraceCompareResult::ok;
    } else {
      return TraceCompareResult::truncated;
    }
  }
  return TraceCompareResult::differs;
}

Module *LoadModule(const string &filename) {

  // Load the bytecode...
  string ErrorMsg;
  auto *ctx = new LLVMContext();
  Module *result = nullptr;
  OwningPtr<MemoryBuffer> BufferPtr;
  llvm::error_code ec=MemoryBuffer::getFileOrSTDIN(filename.c_str(), BufferPtr);
  if (ec) {
    klee_error("error loading program '%s': %s", filename.c_str(), ec.message().c_str());
  }

  result = getLazyBitcodeModule(BufferPtr.get(), *ctx, &ErrorMsg);
  if (result != nullptr) {
    if (result->MaterializeAllPermanently(&ErrorMsg)) {
      delete result;
      result = nullptr;
    }
  }
  if (!result) klee_error("error loading program '%s': %s", filename.c_str(), ErrorMsg.c_str());
  BufferPtr.take();
  return result;
}

map<string,KModule*> module_cache;

KModule *PrepareModule(const string &filename) {

  auto itr = module_cache.find(filename);
  if (itr != module_cache.end()) {
    return itr->second;
  } else {
    if (Module *module = LoadModule(filename)) {
      if (!isPrepared(module)) {
        errs() << "not prepared: " << module->getModuleIdentifier() << '\n';
      } else {
        if (KModule *kmodule = new KModule(module)) {
          kmodule->prepare();
          module_cache.insert(make_pair(filename, kmodule));
          return kmodule;
        }
      }
    }
  }
  return nullptr;
}

#define EXIT_OK               0
#define EXIT_REPLAY_ERROR     1
#define EXIT_STATUS_CONFLICT  2
#define EXIT_TRACE_CONFLICT   3

void expand_test_files(const string &prefix, deque<string> &files) {

  if (ReplayTests.empty()) {
    ReplayTests.push_back(Output);
  }

  for (const auto &str : ReplayTests) {
    fs::path entry(str);
    boost::system::error_code ec;
    fs::file_status s = fs::status(entry, ec);
    if (fs::is_regular_file(s)) {
      files.push_back(str);
    } else if (fs::is_directory(s)) {
      for (fs::directory_iterator itr{entry}, end{}; itr != end; ++itr) {
        // add regular files of the form test*.json
        fs::path pfile(itr->path());
        if (fs::is_regular_file(pfile) &&
           (pfile.extension().string() == ".json") &&
           (boost::starts_with(pfile.filename().string(), prefix))) {

          files.push_back(pfile.string());
        }
      }
    } else {
      errs() << "Entry not found: " << str << '\n';
    }
  }
  sort(files.begin(), files.end());
}

int main(int argc, char **argv, char **envp) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();
  sys::SetInterruptFunction(interrupt_handle);
  exit_code = EXIT_OK;

#ifdef _DEBUG
  EnableMemDebuggingChecks();
#endif // _DEBUG

#ifdef DO_HEAP_PROFILE
  HeapProfilerStart("brt-rply");
#endif

  deque<string> test_files;
  expand_test_files(Prefix, test_files);

  for (const string &test_file : test_files) {

    TestCase test;
    ifstream info;
    Json::Value root;  // needed here if we intend to update later
    info.open(test_file);
    if (info.is_open()) {
      info >> root;
      load_test_case(root, test);
    }
    if (!test.is_ready()) {
      klee_error("failed to load test case '%s'", test_file.c_str());
    }

    outs() << fs::path(test_file).filename().string() << "::" << test.entry_fn << " -> " << oflush;

    string module_name = ModuleName;
    if (module_name.empty()) module_name = test.file_name;
    KModule *kmod = PrepareModule(module_name);
    LLVMContext *ctx = kmod->getContextPtr();

    // Common setup
    Interpreter::InterpreterOptions IOpts;
    IOpts.mode = ExecModeID::rply;
    IOpts.user_mem_base = (void *) 0x90000000000;
    IOpts.user_mem_size = (0xa0000000000 - 0x90000000000);
    IOpts.test_objs = &test.objects;
    IOpts.verbose = Verbose;
    IOpts.trace = test.trace_type;
    if (TraceT != TraceType::invalid) {
      IOpts.trace = TraceT;
    }
    UnconstraintFlagsT flags;
    IOpts.progression.emplace_back(300, flags);

    vector<ExecutionState *> ex_states;
    ReplayKleeHandler *handler = new ReplayKleeHandler(ex_states, kmod->getModuleIdentifier());

    Interpreter *interpreter = Interpreter::createLocal(*ctx, IOpts, handler);
    handler->setInterpreter(interpreter);
    interpreter->bindModule(kmod);

    theInterpreter = interpreter;
    interpreter->runFunctionTestCase(test);
    theInterpreter = nullptr;

    // only used for verbose output
    vector<unsigned char> stdout_capture;
    vector<unsigned char> stderr_capture;

    ExecutionState *state = nullptr;

    if (ex_states.empty()) {
      outs() << "Failed to replay" << oflush;
      exit_code = max(exit_code, EXIT_REPLAY_ERROR);
    } else if (ex_states.size() > 1) {
      outs() << "Replay forked into multiple paths" << oflush;
      exit_code = max(exit_code, EXIT_REPLAY_ERROR);
    } else {
      state = ex_states.front();

      state->stdout_capture.get_data(stdout_capture);
      state->stderr_capture.get_data(stderr_capture);

      if (CheckTrace || UpdateTrace) {
        if (IOpts.trace == test.trace_type) {
          TraceCompareResult res = compare_traces(test.trace, state->trace);
          if ((res == TraceCompareResult::truncated)  || (res == TraceCompareResult::differs)) {
            outs() << "trace " << (res == TraceCompareResult::differs ? "differs, " : "truncated, ");
            exit_code = max(exit_code, EXIT_TRACE_CONFLICT);
            if (UpdateTrace) {
              update_test_case(test_file, root, state->trace);
            }
          }
        } else {
          errs() << "incomparable trace types, ";
          exit_code = max(exit_code, EXIT_TRACE_CONFLICT);
        }
      }

      if (test.status != StateStatus::Snapshot) {

        if (test.status != state->status) {
          outs() << "status differs: test=" << to_string(test.status) << " state=" << to_string(state->status) << oflush;
          exit_code = max(exit_code, EXIT_STATUS_CONFLICT);
        } else {
          outs() << "ok" << oflush;
        }
      } else {
        outs() << to_string(state->status) << oflush;
      }

      if (state->status != StateStatus::Completed) {
        if (!state->messages.empty()) {
          outs() << " (" << state->messages.back() << ')' << oflush;
        }
      }

    }
    outs() << oendf;

    if (state != nullptr) {
      if (TraceT == TraceType::calls) {
        outs() << "Call Trace:\n";
        outs() << test.entry_fn << '\n';

        // build a reverse loop up map of function ids
        map<unsigned, string> fnMap;
        for (auto itr = kmod->functionMap.begin(), end = kmod->functionMap.end(); itr != end; ++itr) {
          Function *fn = itr->first;
          unsigned fnID = kmod->getFunctionID(fn);
          if (fnID != 0) {
            fnMap.insert(make_pair(fnID, fn->getName()));
          }
        }

        int call_depth = 0;
        for (auto entry : state->trace) {
          bool is_call = (entry % 1000) == 1;
          bool is_retn = (entry % 1000) == 2;
          if (is_call) {
            call_depth += 1;
            unsigned fnID = entry / 1000;
            auto itr = fnMap.find(fnID);
            if (itr != fnMap.end()) {
              assert(call_depth >= 0);
              outs().indent(call_depth * 2);
              outs() << itr->second << '\n';
            }
          } else if (is_retn) {
            call_depth -= 1;
          }
        }
      }
    }

    if (ShowOutput) {
      // display captured output
      if (!stdout_capture.empty()) {
        outs() << "stdout: " << toDataString(stdout_capture, 64) << '\n';
        for (auto itr = stdout_capture.begin(), end = stdout_capture.end(); itr != end; ++itr) {
          outs() << *itr;
        }
      }
      if (!stderr_capture.empty()) {
        outs() << "stdout: " << toDataString(stderr_capture, 64) << '\n';
        for (auto itr = stderr_capture.begin(), end = stderr_capture.end(); itr != end; ++itr) {
          outs() << *itr;
        }
      }
    }

    if (ShowFnFreq > 0) {

      // display a sorted list of function call invocations by target fn
      // this can be used to determine when a libc function should be modeled for performance.
      vector<pair<unsigned,const Function*> >fn_counters;
      handler->getCallCounters(fn_counters);
      sort(fn_counters.begin(), fn_counters.end(), greater<pair<unsigned,const Function*> >());
      unsigned idx = 0;
      for (const auto &pr : fn_counters) {
        outs() << pr.second->getName() << ": " << pr.first << oendl;
        if (++idx == ShowFnFreq) break;
      }
    }

    state = nullptr;
    for (auto s : ex_states) {
      delete s;
    }
    ex_states.clear();

    delete interpreter;
    delete handler;
  }

  // clean up the cached modules
  for (auto &pr : module_cache) {
    LLVMContext *ctx = pr.second->getContextPtr();
    delete pr.second;
    delete ctx;
  }

  return exit_code;
}
