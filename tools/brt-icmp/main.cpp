/* -*- mode: c++; c-basic-offset: 2; -*- */

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
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Module/KInstruction.h"
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

#include <signal.h>
#include <unistd.h>
#include <sys/wait.h>

#include <cerrno>
#include <string>
#include <iomanip>
#include <iterator>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include <klee/Internal/Support/ModuleUtil.h>
#include "json/json.h"
#include "klee/TestCase.h"
#include "klee/util/CommonUtil.h"
#include "StateComparison.h"

using namespace llvm;
using namespace klee;
using namespace std;

namespace {
  cl::opt<string> InputFile1(cl::desc("<bytecode1>"), cl::Positional, cl::Required);
  cl::opt<string> InputFile2(cl::desc("<bytecode2>"), cl::Positional);
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<string> ReplayTest("test", cl::desc("test case to replay"), cl::Required);
  cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
  cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));
  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"));
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

size_t compare_traces(const vector<unsigned> &test_trace, const deque<unsigned> &state_trace, size_t length) {

  auto itr_t = test_trace.begin();
  auto end_t = test_trace.end();
  auto itr_s = state_trace.begin();
  auto end_s = state_trace.end();

  size_t index = 0;
  while (itr_t != end_t || itr_s != end_s) {
    if (itr_t == end_t || itr_s == end_s || *itr_t != *itr_s) {
      return index;
    }
    if (++index == length) break;
    ++itr_t;
    ++itr_s;
  }
  return UINT64_MAX;
}

void load_test_case(Json::Value &root, TestCase &test) {

  // complete test case from json structure
  test.arg_c = root["argC"].asInt();
  test.arg_v = root["argV"].asString();

  test.module_name = root["module"].asString();
  test.entry_fn = root["entryFn"].asString();
  test.klee_version = root["kleeRevision"].asString();
  test.lazy_alloc_count = root["lazyAllocationCount"].asUInt();
  test.max_lazy_depth = root["maxLazyDepth"].asUInt();
  test.max_loop_forks = root["maxLoopForks"].asUInt();
  test.max_loop_iter = root["maxLoopIteration"].asUInt();
  test.message = root["message"].asString();
  test.path_condition_vars = root["pathConditionVars"].asString();
  test.status = (StateStatus) root["status"].asUInt();
  test.test_id = root["testID"].asUInt();
  test.start = to_time_point(root["timeStarted"].asString());
  test.stop = to_time_point(root["timeStopped"].asString());

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

int main(int argc, char **argv, char **envp) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();
  sys::SetInterruptFunction(interrupt_handle);
  exit_code = 0;

  // write out command line info, for reference
  if (!outs().is_displayed()) {
    for (int i = 0; i < argc; i++) {
      outs() << argv[i] << (i + 1 < argc ? " " : "\n");
    }
    outs() << "PID: " << getpid() << "\n";
  }

  // Load the test case
  TestCase test;
  if (!ReplayTest.empty()) {

    ifstream info;
    info.open(ReplayTest);
    if (info.is_open()) {

      Json::Value root;
      info >> root;
      load_test_case(root, test);
    }
  }

  if (!test.is_ready()) {
    klee_error("failed to load test case '%s'", ReplayTest.c_str());
  }

  size_t test_trace_length = 0;
  if (test.status == StateStatus::Pending) test_trace_length = test.trace.size();

  // Common setup
  Interpreter::InterpreterOptions IOpts;
  IOpts.mode = ExecModeID::rply;
  IOpts.user_mem_base = (void*) 0x90000000000;
  IOpts.user_mem_size = (0xa0000000000 - 0x90000000000);
  IOpts.trace = test.trace_type;

  Interpreter::ModuleOptions MOpts;
  MOpts.LibraryDir = "";
  MOpts.Optimize = false;
  MOpts.CheckDivZero = false;
  MOpts.CheckOvershift = false;
  MOpts.test = &test;

  string ErrorMsg;
  llvm::error_code ec;
  vector<ExecutionState*> ex_states;

  CompareState version1;

  // Load the bytecode...
  // load the bytecode emitted in the generation step...

  // load the first module
  outs() << "Loading: " << InputFile1 << '\n';
  Module *mainModule1 = nullptr;
  OwningPtr<MemoryBuffer> BufferPtr1;

  ec = MemoryBuffer::getFileOrSTDIN(InputFile1.c_str(), BufferPtr1);
  if (ec) {
    klee_error("error loading program '%s': %s", InputFile1.c_str(), ec.message().c_str());
  }

  LLVMContext ctx1;
  mainModule1 = getLazyBitcodeModule(BufferPtr1.get(), ctx1, &ErrorMsg);

  if (mainModule1) {
    if (mainModule1->MaterializeAllPermanently(&ErrorMsg)) {
      delete mainModule1;
      mainModule1 = nullptr;
    }
  }

  if (!mainModule1) klee_error("error loading program '%s': %s", InputFile1.c_str(), ErrorMsg.c_str());
  if (!isPrepared(mainModule1)) klee_error("program is not prepared '%s'", InputFile1.c_str());

  ReplayKleeHandler *handler1 = new ReplayKleeHandler(ex_states, mainModule1->getModuleIdentifier());

  Interpreter *interpreter1 = Interpreter::createLocal(ctx1, IOpts, handler1);
  handler1->setInterpreter(interpreter1);
  interpreter1->setModule(mainModule1, MOpts);

  auto start_time = sys_clock::now();
  outs() << "Started: " << to_string(start_time) << '\n';
  outs().flush();

  theInterpreter = interpreter1;
  interpreter1->runFunctionTestCase(test);
  theInterpreter = nullptr;

  auto finish_time = sys_clock::now();
  outs() << "Finished: " << to_string(finish_time) << '\n';
  auto elapsed = chrono::duration_cast<chrono::seconds>(finish_time - start_time);
  outs() << "Elapsed: " << elapsed.count() << '\n';

  version1.kmodule = interpreter1->getKModule();
  assert(ex_states.size() == 1);
  version1.state = ex_states.front();
  ex_states.clear();

  if (test.status != StateStatus::Snapshot && handler1->getModuleName() == test.module_name) {
    size_t index = compare_traces(test.trace, version1.state->trace, test_trace_length);
    if (index != UINT64_MAX) {
      errs() << "replay diverged at index " << index << '\n';
    }
  }

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  // FIXME: This really doesn't look right
  // This is preventing the module from being
  // deleted automatically
  BufferPtr1.take();
#endif


  // now, lets do it all again with the second module
  if (InputFile2.size() > 0) {
    CompareState version2;

    outs() << "Loading: " << InputFile2 << '\n';
    Module *mainModule2 = nullptr;
    OwningPtr<MemoryBuffer> BufferPtr2;
    ec = MemoryBuffer::getFileOrSTDIN(InputFile2.c_str(), BufferPtr2);
    if (ec) {
      klee_error("error loading program '%s': %s", InputFile2.c_str(), ec.message().c_str());
    }

    LLVMContext ctx2;
    mainModule2 = getLazyBitcodeModule(BufferPtr2.get(), ctx2, &ErrorMsg);
    if (mainModule2) {
      if (mainModule2->MaterializeAllPermanently(&ErrorMsg)) {
        delete mainModule2;
        mainModule2 = nullptr;
      }
    }

    if (!mainModule2) klee_error("error loading program '%s': %s", InputFile2.c_str(), ErrorMsg.c_str());
    if (!isPrepared(mainModule2)) klee_error("program is not prepared '%s':", InputFile2.c_str());

    ReplayKleeHandler *handler2 = new ReplayKleeHandler(ex_states, mainModule2->getModuleIdentifier());

    Interpreter *interpreter2 = Interpreter::createLocal(ctx2, IOpts, handler2);
    handler2->setInterpreter(interpreter2);
    interpreter2->setModule(mainModule2, MOpts);

    start_time = sys_clock::now();
    outs() << "Started: " << to_string(start_time) << '\n';
    outs().flush();

    theInterpreter = interpreter2;
    interpreter2->runFunctionTestCase(test);
    theInterpreter = nullptr;

    finish_time = sys_clock::now();
    outs() << "Finished: " << to_string(finish_time) << '\n';
    elapsed = chrono::duration_cast<chrono::seconds>(finish_time - start_time);
    outs() << "Elapsed: " << elapsed.count() << '\n';

    version2.kmodule = interpreter2->getKModule();
    assert(ex_states.size() == 1);
    version2.state = ex_states.front();
    ex_states.clear();

    if (handler2->getModuleName() == test.module_name) {
      size_t index = compare_traces(test.trace, version2.state->trace, test_trace_length);
      if (index != UINT64_MAX) {
        errs() << "replay diverged at index " << index << '\n';
      }
    }

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
    // FIXME: This really doesn't look right
    // This is preventing the module from being
    // deleted automatically
    BufferPtr2.take();
  #endif

    if (!CompareExecutions(version1, version2)) {
      outs() << "Behavioral Discrepancy\n";
      exit_code = 1;
    }
  }

  return exit_code;
}
