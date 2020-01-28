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
#include "klee/Statistics.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/Support/Debug.h"
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

#ifdef _DEBUG
#include <gperftools/tcmalloc.h>
#include <gperftools/heap-profiler.h>
#include <gperftools/heap-checker.h>
#endif

using namespace llvm;
using namespace klee;
using namespace std;
namespace fs=boost::filesystem;

namespace {
  cl::list<string> ReplayTests(cl::desc("<test case to replay>"), cl::Positional, cl::OneOrMore);
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
  cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));
  cl::opt<bool> CheckTrace("check-trace", cl::desc("compare executed trace to test case"), cl::init(false));
  cl::opt<bool> UpdateTrace("update-trace", cl::desc("update test case trace, if differs from replay"), cl::init(false));
  cl::opt<bool> Verbose("verbose", cl::desc("Display additional information about replay"), cl::init(false));
  cl::opt<TraceType> TraceT("trace",
                            cl::desc("Choose the type of trace (default=marked basic blocks"),
                            cl::values(clEnumValN(TraceType::none, "none", "do not trace execution"),
                                       clEnumValN(TraceType::bblocks, "bblk", "trace execution by basic block"),
                                       clEnumValN(TraceType::statements, "stmt", "trace execution by source statement"),
                                       clEnumValN(TraceType::assembly, "assm", "trace execution by assembly line"),
                                       clEnumValEnd),
                            cl::init(TraceType::invalid));

}

/***/

class ReplayKleeHandler : public InterpreterHandler {
private:
  string indentation;
  boost::filesystem::path outputDirectory;
  string md_name;
  vector<ExecutionState*> &results;

public:
  ReplayKleeHandler(vector<ExecutionState*> &_results, const string &_md_name);
  ~ReplayKleeHandler();

  void setInterpreter(Interpreter *i) override;

  void processTestCase(ExecutionState  &state) override;

  string toDataString(const vector<unsigned char> &data) const;

  string getOutputFilename(const string &filename) override;
  string getTestFilename(const string &prefix, const string &ext, unsigned id);
  string getModuleName() const override { return md_name; }

  ostream *openTestCaseFile(const string &prefix, unsigned testID);
  llvm::raw_fd_ostream *openTestFile(const string &prefix, const string &ext, unsigned id);
  llvm::raw_fd_ostream *openOutputFile(const string &filename, bool overwrite=false) override;

  static string getRunTimeLibraryPath(const char *argv0);

};

ReplayKleeHandler::ReplayKleeHandler(vector<ExecutionState*> &_results, const string &_md_name)
  : indentation(""),
    outputDirectory(Output),
    results(_results) {

  assert(results.empty());

  if (IndentJson) indentation = "  ";
}

ReplayKleeHandler::~ReplayKleeHandler() {
}

void ReplayKleeHandler::setInterpreter(Interpreter *i) {
  InterpreterHandler::setInterpreter(i);
}

string ReplayKleeHandler::getOutputFilename(const string &filename) {

  boost::filesystem::path file = outputDirectory;
  file /= filename;
  return file.string();
}

llvm::raw_fd_ostream *ReplayKleeHandler::openOutputFile(const string &filename, bool overwrite) {
  llvm::raw_fd_ostream *f;
  string Error;
  string path = getOutputFilename(filename);
#if LLVM_VERSION_CODE >= LLVM_VERSION(3,5)
  f = new llvm::raw_fd_ostream(path.c_str(), Error, llvm::sys::fs::F_None);
#else
  llvm::sys::fs::OpenFlags fs_options = llvm::sys::fs::F_Binary;
  if (overwrite) {
    fs_options |= llvm::sys::fs::F_Excl;
  }
  f = new llvm::raw_fd_ostream(path.c_str(), Error, fs_options);
#endif
  if (!Error.empty()) {
    if (!boost::algorithm::ends_with(Error, "File exists")) {
      klee_warning("error opening file \"%s\".  KLEE may have run out of file "
                   "descriptors: try to increase the maximum number of open file "
                   "descriptors by using ulimit (%s).",
                   filename.c_str(), Error.c_str());
    }
    delete f;
    f = nullptr;
  }
  return f;
}

string ReplayKleeHandler::getTestFilename(const string &prefix, const string &ext, unsigned id) {
  stringstream filename;
  filename << prefix << setfill('0') << setw(10) << id << '.' << ext;
  return filename.str();
}

llvm::raw_fd_ostream *ReplayKleeHandler::openTestFile(const string &prefix, const string &ext, unsigned id) {
  return openOutputFile(getTestFilename(prefix, ext, id));
}

ostream *ReplayKleeHandler::openTestCaseFile(const string &prefix, unsigned testID) {

  ofstream *result = nullptr;
  string filename = getOutputFilename(getTestFilename(prefix, "json", testID));
  result = new ofstream(filename);
  if (result != nullptr) {
    if (!result->is_open()) {
      delete result;
      result = nullptr;
    }
  }
  return result;
}

string ReplayKleeHandler::toDataString(const vector<unsigned char> &data) const {

  stringstream bytes;
  for (auto itrData = data.begin(), endData = data.end(); itrData != endData; ++itrData) {

    unsigned char hi = (unsigned char) (*itrData >> 4);
    unsigned char low = (unsigned char) (*itrData & 0x0F);
    hi = (unsigned char) ((hi > 9) ? ('A' + (hi - 10)) : ('0' + hi));
    low = (unsigned char) ((low > 9) ? ('A' + (low - 10)) : ('0' + low));
    bytes << hi << low;
  }
  return bytes.str();
}

void ReplayKleeHandler::processTestCase(ExecutionState &state) {

  results.push_back(new ExecutionState(state));
}

string ReplayKleeHandler::getRunTimeLibraryPath(const char *argv0) {
  // allow specifying the path to the runtime library
  const char *env = getenv("KLEE_RUNTIME_LIBRARY_PATH");
  if (env) {
    return string(env);
  }

  if (strlen(KLEE_INSTALL_RUNTIME_DIR) > 0) {
    return string(KLEE_INSTALL_RUNTIME_DIR);
  }

  // Take any function from the execution binary but not main (as not allowed by
  // C++ standard)
  void *MainExecAddr = (void *)(intptr_t)getRunTimeLibraryPath;
  SmallString<128> toolRoot(
      llvm::sys::fs::getMainExecutable(argv0, MainExecAddr)
      );

  // Strip off executable so we have a directory path
  llvm::sys::path::remove_filename(toolRoot);

  SmallString<128> libDir;

  if (strlen( KLEE_INSTALL_BIN_DIR ) != 0 &&
      strlen( KLEE_INSTALL_RUNTIME_DIR ) != 0 &&
      toolRoot.str().endswith( KLEE_INSTALL_BIN_DIR ))
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using installed KLEE library runtime: ");
    libDir = toolRoot.str().substr(0,
               toolRoot.str().size() - strlen( KLEE_INSTALL_BIN_DIR ));
    llvm::sys::path::append(libDir, KLEE_INSTALL_RUNTIME_DIR);
  }
  else
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using build directory KLEE library runtime :");
    libDir = KLEE_DIR;
    llvm::sys::path::append(libDir,RUNTIME_CONFIGURATION);
    llvm::sys::path::append(libDir,"lib");
  }

  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                       libDir.c_str() << "\n");
  return libDir.str();
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
  TestObject::fromDataString(test.stdin_buffer, root["stdin"].asString());

  Json::Value &args = root["arguments"];
  if (args.isArray()) {
    test.arguments.reserve(args.size());
    for (unsigned idx = 0, end = args.size(); idx < end; ++idx) {
      string value = args[idx].asString();
      vector<unsigned char> bytes;
      TestObject::fromDataString(bytes, value);
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

bool compare_traces(const vector<unsigned> &t_trace, const deque<unsigned> &s_trace) {

  if (t_trace.size() == s_trace.size()) {
    auto t_itr = t_trace.begin();
    auto t_end = t_trace.end();
    auto s_itr = s_trace.begin();
    auto s_end = s_trace.end();
    while (t_itr != t_end) {
      assert(s_itr != s_end);
      if (*t_itr++ != *s_itr++) return false;
    }
    return true;
  }
  return false;
}

string to_string(const vector<unsigned char> &buffer, unsigned max = 256) {
  unsigned counter = 0;
  ostringstream bytes;
  for (auto itr = buffer.begin(), end = buffer.end(); (itr != end) && (counter++ < max); ++itr) {

    unsigned char hi = (unsigned char) (*itr >> 4);
    unsigned char low = (unsigned char) (*itr & 0x0F);
    hi = (unsigned char) ((hi > 9) ? ('A' + (hi - 10)) : ('0' + hi));
    low = (unsigned char) ((low > 9) ? ('A' + (low - 10)) : ('0' + low));
    bytes << hi << low;
  }
  return bytes.str();
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

//#define DO_HEAP_PROFILE 1

#define EXIT_OK               0
#define EXIT_REPLAY_ERROR     1
#define EXIT_STATUS_CONFLICT  2
#define EXIT_TRACE_CONFLICT   3

void expand_test_files(deque<string> &files) {

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
           (boost::starts_with(pfile.filename().string(), "test"))) {

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
  expand_test_files(test_files);

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
    KModule *kmod = PrepareModule(test.file_name);
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
    map<unsigned, unsigned> counters;

    outs() << fs::path(test_file).filename().string() << "::" << test.entry_fn << " -> ";

    if (ex_states.empty()) {
      errs() << "Failed to replay";
      exit_code = max(exit_code, EXIT_REPLAY_ERROR);
    } else if (ex_states.size() > 1) {
      errs() << "Replay forked into multiple paths";
      exit_code = max(exit_code, EXIT_REPLAY_ERROR);
    } else {
      ExecutionState *state = ex_states.front();

      if (Verbose) {
        state->stdout_capture.get_data(stdout_capture);
        state->stderr_capture.get_data(stderr_capture);
        // count fn markers in the trace
        for (unsigned mark : state->trace) {
          counters[mark / 1000] += 1;
        }
      }

      if (CheckTrace || UpdateTrace) {
        if (IOpts.trace == test.trace_type) {
          if (!compare_traces(test.trace, state->trace)) {
            outs() << "trace differs, ";
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

      if (test.status != state->status) {
        outs() << "status differs: test=" << to_string(test.status) << " state=" << to_string(state->status);
        exit_code = max(exit_code, EXIT_STATUS_CONFLICT);
      } else {
        outs() << "ok";
      }

      if (state->status != StateStatus::Completed) {
        outs() << " (" << state->terminationMessage << ')';
      }

    }
    outs() << '\n';

    if (Verbose) {
      // display captured output
      if (!stdout_capture.empty()) {
        outs() << "stdout: " << to_string(stdout_capture, 64) << '\n';
      }
      if (!stderr_capture.empty()) {
        outs() << "stdout: " << to_string(stderr_capture, 64) << '\n';
      }

      // build an inverse map of fnIDs
      //    KModule *kmodule = interpreter->getKModule();
      //    Module *module = kmodule->module;
      //    map<unsigned,string> fnIDtoName;
      //    for (auto itr = module->begin(), end = module->end(); itr != end; ++itr) {
      //      Function *fn = itr;
      //      unsigned fnID = kmodule->getFunctionID(fn);
      //      if (fnID != 0) {
      //        fnIDtoName[fnID] = fn->getName().str();
      //      }
      //    }
      //
      //    // display a sorted list of trace statements from each block.
      //    // this can be used to determine when a libc function should be modeled for performance.
      //    vector<pair<unsigned,unsigned> >fn_counter;
      //    fn_counter.reserve(counters.size());
      //    for (auto &itr : counters) {
      //      fn_counter.emplace_back(make_pair(itr.second, itr.first));
      //    }
      //    sort(fn_counter.begin(), fn_counter.end(), greater<pair<unsigned,unsigned> >());
      //    for (const auto &pr : fn_counter) {
      //      outs() << fnIDtoName[pr.second] << ": " << pr.first << '\n';
      //    }
    }

    for (auto state : ex_states) {
      delete state;
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
