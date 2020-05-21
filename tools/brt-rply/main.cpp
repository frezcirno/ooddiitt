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
  cl::opt<bool> ShowTrace("show-trace", cl::desc("display replay's trace"));
  cl::opt<bool> InstrCounters("instr-counters", cl::desc("update test case file with count of instructions executed per function"));
  cl::opt<bool> Verbose("verbose", cl::desc("Display additional information about replay"));
  cl::opt<string> ModuleName("module", cl::desc("override module specified by test case"));
  cl::opt<string> DiffInfo("diff-info", cl::desc("json formated diff file"));
  cl::opt<string> Prefix("prefix", cl::desc("prefix for loaded test cases"), cl::init("test"));
  cl::opt<unsigned> Timeout("timeout", cl::desc("maximum seconds to replay"), cl::init(10));
  cl::opt<bool> ShowArgs("show-args", cl::desc("show invocation command line args"));
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
  vector<pair<ExecutionState*,TerminateReason> > &results;

public:
  ReplayKleeHandler(vector<pair<ExecutionState*,TerminateReason> > &_results, const string &_md_name)
    : InterpreterHandler(Output, _md_name), indentation(""), results(_results) {
    assert(results.empty());
    if (IndentJson) indentation = "  ";
  }

  ~ReplayKleeHandler() override = default;

  void onStateFinalize(ExecutionState &state, TerminateReason reason) override  {
    results.push_back(make_pair(new ExecutionState(state), reason));
  }
};

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
  test.term_reason = (TerminateReason) root["termination"].asUInt();
  test.test_id = root["testID"].asUInt();
  test.start = to_time_point(root["timeStarted"].asString());
  test.stop = to_time_point(root["timeStopped"].asString());
  fromDataString(test.stdin_buffer, root["stdin"].asString());
  test.unconstraintFlags = UnconstraintFlagsT(root["unconstraintFlags"].asString());

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
      test.trace.push_back(trace[idx].asString());
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

bool update_test_case(const string &fname, Json::Value &root) {

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

void load_diff_info(const string &diff_file, KModule *kmod) {

  string filename = diff_file;
  if (filename.empty()) {
    filename = (fs::path(Output)/"diff.json").string();
  }
  ifstream infile(filename);
  if (infile.is_open()) {
    Json::Value root;
    infile >> root;

    string module_name = fs::path(kmod->getModuleIdentifier()).filename().string();
    kmod->pre_module = root["pre-module"].asString();
    kmod->post_module = root["post-module"].asString();
    kmod->is_pre_module = (kmod->pre_module == module_name);

    Json::Value &fns = root["functions"];
    Json::Value &fns_added = fns["added"];
    for (unsigned idx = 0, end = fns_added.size(); idx < end; ++idx) {
      kmod->addDiffFnAdded(fns_added[idx].asString());
    }
    Json::Value &fns_removed = fns["removed"];
    for (unsigned idx = 0, end = fns_removed.size(); idx < end; ++idx) {
      kmod->addDiffFnRemoved(fns_removed[idx].asString());
    }
    Json::Value &fns_body = fns["body"];
    for (unsigned idx = 0, end = fns_body.size(); idx < end; ++idx) {
      string str = fns_body[idx].asString();
      kmod->addDiffFnChangedBody(str);
    }
    Json::Value &fns_sig = fns["signature"];
    for (unsigned idx = 0, end = fns_sig.size(); idx < end; ++idx) {
      string str = fns_sig[idx].asString();
      kmod->addDiffFnChangedSig(str);
    }

    Json::Value &gbs = root["globals"];
    Json::Value &gbs_added = gbs["added"];
    for (unsigned idx = 0, end = gbs_added.size(); idx < end; ++idx) {
      kmod->addDiffGlobalAdded(gbs_added[idx].asString());
    }
    Json::Value &gbs_removed = gbs["removed"];
    for (unsigned idx = 0, end = gbs_removed.size(); idx < end; ++idx) {
      kmod->addDiffGlobalRemoved(gbs_removed[idx].asString());
    }

    Json::Value &gbs_type = gbs["changed"];
    for (unsigned idx = 0, end = gbs_type.size(); idx < end; ++idx) {
      string str = gbs_type[idx].asString();
      kmod->addDiffGlobalChanged(str);
    }

    string targeted_key = (kmod->isPreModule() ? "pre_src_lines" : "post_src_lines");
    Json::Value &tgt_src = root[targeted_key];
    for (auto src_itr = tgt_src.begin(), src_end = tgt_src.end(); src_itr != src_end; ++src_itr) {
      string src_file = src_itr.key().asString();
      Json::Value &stmt_array = *src_itr;
      if (stmt_array.isArray()) {
        set<unsigned> &stmts = kmod->getTargetedSrc(src_file);
        for (unsigned idx = 0, end = stmt_array.size(); idx < end; ++idx) {
          stmts.insert(stmt_array[idx].asUInt());
        }
      }
    }
  } else {
    klee_warning("failed opening diff file: %s", filename.c_str());
  }
}

enum class TraceCompareResult { ok, truncated, differs };

TraceCompareResult compare_traces(const vector<string> &t_trace, const TraceDequeT &s_trace) {

  vector<string> tmp;
  tmp.reserve(s_trace.size());
  for (const auto &entry : s_trace) {
    tmp.push_back(to_string(entry));
  }

  if (boost::starts_with(t_trace, tmp)) {
    if (t_trace.size() == tmp.size()) {
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
    klee_error("failure loading program '%s': %s", filename.c_str(), ec.message().c_str());
  }

  result = getLazyBitcodeModule(BufferPtr.get(), *ctx, &ErrorMsg);
  if (result != nullptr) {
    if (result->MaterializeAllPermanently(&ErrorMsg)) {
      delete result;
      result = nullptr;
    }
  }
  if (!result) {
    klee_error("failure materializing program '%s': %s", filename.c_str(), ErrorMsg.c_str());
  }
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
        klee_error("not prepared: %s", module->getModuleIdentifier().c_str());
      } else {
        if (KModule *kmodule = new KModule(module)) {
          kmodule->prepare();
          load_diff_info(DiffInfo, kmodule);
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

  // if tests are not specified, then default to all tests in the output directory
  if (ReplayTests.empty()) {
    ReplayTests.push_back(Output);
  }
  deque<string> worklist(ReplayTests.begin(), ReplayTests.end());
  string annotated_prefix = prefix + '-';

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
        if (fs::is_regular_file(pfile) &&
           (pfile.extension().string() == ".json") &&
           (boost::starts_with(pfile.filename().string(), annotated_prefix))) {

          files.push_back(pfile.string());
        }
      }
    } else if (entry.parent_path().empty()) {
      // only filename given, try the output directory
      worklist.push_back((Output/entry).string());
    } else {
      errs() << "Entry not found: " << str << '\n';
    }
  }
  sort(files.begin(), files.end());
}

void getModuleName(const string &dir, string &name) {

  // if cmd line arg does not end in .bc, this could be a prefix
  // look for a matching bitcode file in the output directory
  if (!boost::ends_with(name, ".bc")) {
    string prefix = name + '-';
    for (fs::directory_iterator itr{dir}, end{}; itr != end; ++itr) {
      fs::path pfile(itr->path());
      if (fs::is_regular_file(pfile) && (pfile.extension().string() == ".bc")) {
        string filename = pfile.filename().string();
        if (boost::starts_with(filename, prefix)) {
          name = pfile.string();
          break;
        }
      }
    }
  }
}


static const char *err_context = nullptr;
static void PrintStackTraceSignalHandler(void *) {
  if (err_context != nullptr) {
    fprintf(stderr, "context: %s\n", err_context);
  }
  sys::PrintStackTrace(stderr);
}

int main(int argc, char **argv, char **envp) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::AddSignalHandler(PrintStackTraceSignalHandler, nullptr);
  sys::SetInterruptFunction(interrupt_handle);

  // write out command line info, for reference
  if (ShowArgs) show_args(argc, argv);

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

    outs() << fs::path(test_file).filename().string() << ':' << oflush;
    err_context = test_file.c_str();

    string module_name = ModuleName;
    if (module_name.empty()) {
      module_name = test.file_name;
    } else {
      getModuleName(Output, module_name);
    }

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

    if (InstrCounters) {
      IOpts.fn_instr_counters = new map<Function*,uint64_t>;
    }

    UnconstraintFlagsT flags;
    IOpts.progression.emplace_back(Timeout, flags);

    vector<pair<ExecutionState*,TerminateReason> > ex_states;
    ReplayKleeHandler *handler = new ReplayKleeHandler(ex_states, kmod->getModuleIdentifier());

    Interpreter *interpreter = Interpreter::createLocal(*ctx, IOpts, handler);
    handler->setInterpreter(interpreter);
    interpreter->bindModule(kmod);

    theInterpreter = interpreter;
    auto start_time = sys_clock::now();
    interpreter->runFunctionTestCase(test);
    theInterpreter = nullptr;
    auto elapsed = chrono::duration_cast<chrono::milliseconds>(sys_clock::now() - start_time);

    ExecutionState *state = nullptr;

    if (ex_states.empty()) {
      outs() << fs::path(kmod->getModuleIdentifier()).stem().string() << ':';
      outs() << (unsigned) TerminateReason::Invalid << ':' << 0 << ':' << elapsed.count() << oendf;
      exit_code = max(exit_code, EXIT_REPLAY_ERROR);
    } else if (ex_states.size() > 1) {
      outs() << fs::path(kmod->getModuleIdentifier()).stem().string() << ':';
      outs() << (unsigned) TerminateReason::FailedLibcInit << ':' << 0 << ':' << elapsed.count() << oendf;
      exit_code = max(exit_code, EXIT_REPLAY_ERROR);
    } else {
      state = ex_states.front().first;
      TerminateReason term_reason = ex_states.front().second;

      assert(state->status == StateStatus::Completed);
      outs() << fs::path(kmod->getModuleIdentifier()).stem().string() << ':';
      outs() << (unsigned) term_reason << ':' << state->reached_target << ':' << elapsed.count() << oendf;

      bool is_dirty = false;
      if (CheckTrace || UpdateTrace) {
        if (IOpts.trace == test.trace_type) {
          TraceCompareResult res = compare_traces(test.trace, state->trace);
          if ((res == TraceCompareResult::truncated)  || (res == TraceCompareResult::differs)) {
            outs() << "trace " << (res == TraceCompareResult::differs ? "differs, " : "truncated, ");
            exit_code = max(exit_code, EXIT_TRACE_CONFLICT);
            if (UpdateTrace) {

              Json::Value &rtrace = root["replayTrace"] = Json::arrayValue;
              for (const auto &entry : state->trace) {
                rtrace.append(to_string(entry));
              }
              is_dirty = true;
            }
          }
        } else {
          errs() << "incomparable trace types, ";
          exit_code = max(exit_code, EXIT_TRACE_CONFLICT);
        }
      }

      if (auto *counters = IOpts.fn_instr_counters) {
        Json::Value &instr = root["instrCounters"] = Json::objectValue;
        for (const auto &pr : *counters) {
          string name = pr.first->getName().str();
          instr[name] = pr.second;
        }
        counters->clear();
        is_dirty = true;
      }

      if (is_dirty) {
        is_dirty = false;
        update_test_case(test_file, root);
      }

      if (Verbose) {
        if (state->instFaulting != nullptr) {
          outs() << "#Faulting statement at " << state->instFaulting->info->file << ':' << state->instFaulting->info->line << oendl;
        }
      }
      if (ShowOutput) {

        // display captured output
        vector<unsigned char> stdout_capture;
        state->stdout_capture.get_data(stdout_capture);
        if (!stdout_capture.empty()) {
          outs() << "stdout: " << toDataString(stdout_capture, 64) << '\n';
          for (auto itr = stdout_capture.begin(), end = stdout_capture.end(); itr != end; ++itr) {
            outs() << *itr;
          }
        }

        vector<unsigned char> stderr_capture;
        state->stderr_capture.get_data(stderr_capture);
        if (!stderr_capture.empty()) {
          outs() << "stdout: " << toDataString(stderr_capture, 64) << '\n';
          for (auto itr = stderr_capture.begin(), end = stderr_capture.end(); itr != end; ++itr) {
            outs() << *itr;
          }
        }
      }

      if (ShowTrace) {
        outs() << "trace:" << oendl;
        for (const auto &entry : state->trace) {
          outs() << to_string(entry) << oendl;
        }
      }
    }

    state = nullptr;
    for (auto s : ex_states) {
      delete s.first;
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
