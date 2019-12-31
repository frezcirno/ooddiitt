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

using namespace llvm;
using namespace klee;
using namespace std;
using namespace boost::algorithm;

namespace bfs = boost::filesystem;

namespace {
  cl::opt<string> TestDirectory(cl::desc("<test case to replay>"), cl::Positional, cl::Required);
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
  cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));
  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"));
}

#define ELEVATE_EXITCODE(c, v)  { if (c < v) c = v; }
#define EXITCODE_OK       0
#define EXITCODE_DIVERGED 1
#define EXITCODE_FORKED   2
#define EXITCODE_FAULTED  3

/***/

class ReplayKleeHandler : public InterpreterHandler {
private:
  string indentation;
  bfs::path outputDirectory;
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

  bfs::path file = outputDirectory;
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
    if (!ends_with(Error, "File exists")) {
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


static int exit_code = EXITCODE_OK;

static void interrupt_handle() {

  if (theInterpreter == nullptr) {
    llvm::errs() << "KLEE: ctrl-c received without interpreter\n";
  } else {
    if (!interrupted) {
      llvm::errs() << "KLEE: ctrl-c detected, requesting interpreter to halt.\n";
      halt_execution();
      sys::SetInterruptFunction(interrupt_handle);
      exit_code = EXITCODE_FAULTED;
    } else {
      llvm::errs() << "KLEE: 2nd ctrl-c detected, exiting.\n";
      exit(4);
    }
    interrupted = true;
  }
}

bool compare_traces(const vector<unsigned> &test_trace, const deque<unsigned> &state_trace, size_t length = 0) {

  // if length is zero, then return if the traces are identical
  if (length == 0) {
    if (test_trace.size() != state_trace.size()) {
      return false;
    }
    length = test_trace.size();
  } else {

    // if length is not zero, then only compare up to length trace elements
    if (test_trace.size() < length || state_trace.size() < length) {
      return false;
    }
  }

  auto itr_t = test_trace.begin();
  auto itr_s = state_trace.begin();

  for (size_t index = 0; index < length; ++index) {
    if (*itr_t++ != *itr_s++) {
      return false;
    }
  }
  return true;
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

void update_test_case(Json::Value &root, StateStatus status, const deque<unsigned> &trace) {

  // update test case status and trace values
  root["status"] = (unsigned) status;
  Json::Value &t = root["trace"] = Json::arrayValue;
  for (auto entry : trace) {
    t.append(entry);
  }
}

typedef pair<LLVMContext*,Module*> ModulePair;

ModulePair LoadModule(const string &filename) {

  ModulePair result;
  string ErrorMsg;

  outs() << "Loading: " << filename << '\n';
  LLVMContext *ctx = new LLVMContext();

  OwningPtr<MemoryBuffer> BufferPtr;
  llvm::error_code ec = MemoryBuffer::getFileOrSTDIN(filename.c_str(), BufferPtr);
  if (ec) {
    klee_error("error loading program '%s': %s", filename.c_str(), ec.message().c_str());
  }
  Module *module = getLazyBitcodeModule(BufferPtr.get(), *ctx, &ErrorMsg);
  if (module) {
    if (module->MaterializeAllPermanently(&ErrorMsg)) {
      delete module;
      module = nullptr;
    }
  }

  if (!module)
    klee_error("error loading program '%s': %s", filename.c_str(), ErrorMsg.c_str());
  if (!isPrepared(module))
    klee_error("program is not prepared '%s'", filename.c_str());

  BufferPtr.take();
  result.first = ctx;
  result.second = module;
  return result;
}

int main(int argc, char **argv, char **envp) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();
  sys::SetInterruptFunction(interrupt_handle);

  set<string> filenames;
  set<string> modules;
  for (bfs::directory_entry &entry : bfs::directory_iterator(TestDirectory)) {
    bfs::path path = entry.path();
    string filename = path.filename().string();
    if (starts_with(filename, "test") && ends_with(filename, ".json")) {
      filenames.insert(path.string());
    } else if (ends_with(filename, ".bc")) {
      modules.insert(path.string());
    }
  }

  map<string,ModulePair> moduleCache;

  // pre-load the module cache with all modules found in output directory
  for (const auto &module : modules) {
    ModulePair mp = LoadModule(module);
    moduleCache.insert(make_pair(module, mp));
  }

  for (const string &fname : filenames) {

    outs() << fname << ": ";

    // Load the test case
    TestCase test;
    Json::Value root;

    ifstream info;
    info.open(fname);
    if (info.is_open()) {

      info >> root;
      load_test_case(root, test);
    }

    if (!test.is_ready()) {
      klee_error("failed to load test case '%s'", fname.c_str());
    }

    // Common setup
    Interpreter::InterpreterOptions IOpts;
    IOpts.mode = ExecModeID::rply;
    IOpts.user_mem_base = (void *) 0x90000000000;
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
    vector<ExecutionState *> ex_states;

    // get the input file from the test case
    string InputFile = test.file_name;

    // Load the bytecode...
    // load the bytecode emitted in the generation step...
    LLVMContext *ctx = nullptr;
    Module *mainModule = nullptr;

    // look in cache for the module
    auto itr = moduleCache.find(InputFile);
    if (itr != moduleCache.end()) {
      ctx = itr->second.first;
      mainModule = itr->second.second;
    } else {
      ModulePair mp = LoadModule(InputFile);
      moduleCache.insert(make_pair(InputFile, mp));
      ctx = mp.first;
      mainModule = mp.second;
    }

    ReplayKleeHandler *handler = new ReplayKleeHandler(ex_states, mainModule->getModuleIdentifier());

    Interpreter *interpreter = Interpreter::createLocal(*ctx, IOpts, handler);
    handler->setInterpreter(interpreter);
    interpreter->setModule(mainModule, MOpts);

    theInterpreter = interpreter;
    interpreter->runFunctionTestCase(test);
    theInterpreter = nullptr;

    if (ex_states.size() != 1) {
      outs() << "forked";
      ELEVATE_EXITCODE(exit_code, EXITCODE_FORKED);
    } else {
      ExecutionState *state = ex_states[0];
      if (test.status == StateStatus::Pending) {
        if (!compare_traces(test.trace, state->trace, test.trace.size())) {
          outs() << "diverged";
          ELEVATE_EXITCODE(exit_code, EXITCODE_DIVERGED);
        } else {

          // rewrite the incomplete test case with full trace and completed state status
          ofstream info;
          info.open(fname);
          if (info.is_open()) {

            update_test_case(root, state->status, state->trace);

            string indentation = "";
            if (IndentJson)
              indentation = "  ";

            Json::StreamWriterBuilder builder;
            builder["commentStyle"] = "None";
            builder["indentation"] = indentation;
            unique_ptr<Json::StreamWriter> writer(builder.newStreamWriter());
            writer.get()->write(root, &info);
            info << endl;
          }
          outs() << "updated";
        }
      } else {
        if (!compare_traces(test.trace, state->trace)) {
          outs() << "diverged";
          ELEVATE_EXITCODE(exit_code, EXITCODE_DIVERGED);
        } else {
          outs() << "ok";
        }
      }
    }

    ex_states.clear();
    outs() << '\n';
  }

  for (auto itr : moduleCache) {
    // deleting the context will also delete its associated module
    delete itr.second.first;
  }

  return exit_code;
}
