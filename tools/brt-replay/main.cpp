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
  cl::opt<string> ReplayTest("replay-test", cl::desc("test case to replay"), cl::Required);
  cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
  cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));
  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-klee-tmp"));
  cl::opt<unsigned> Watchdog("watchdog", cl::desc("Use a watchdog process to monitor se. (default = 0 secs"), cl::init(0));
}

/***/

class ReplayKleeHandler : public InterpreterHandler {
private:
  unsigned casesGenerated;
  string indentation;
  unsigned m_pathsExplored; // number of paths explored so far
  pid_t pid_watchdog;

  boost::filesystem::path outputDirectory;
  map<string,unsigned> terminationCounters;
  string md_name;
  vector<ExecutionState*> &results;

public:
  ReplayKleeHandler(vector<ExecutionState*> &_results, const string &_md_name);
  ~ReplayKleeHandler();

  unsigned getNumTestCases() const override { return casesGenerated; }

  unsigned getNumPathsExplored() { return m_pathsExplored; }
  void incPathsExplored() override { m_pathsExplored++; }

  void setInterpreter(Interpreter *i) override;

  void processTestCase(ExecutionState  &state) override;

  string toDataString(const vector<unsigned char> &data) const;

  string getOutputFilename(const string &filename) override;
  string getTestFilename(const string &prefix, const string &ext, unsigned id);
  string getModuleName() const override { return md_name; }

  ostream *openTestCaseFile(const string &prefix, unsigned testID);
  llvm::raw_fd_ostream *openTestFile(const string &prefix, const string &ext, unsigned id);
  llvm::raw_fd_ostream *openOutputFile(const string &filename, bool overwrite=false) override;

  bool resetWatchDogTimer() const override;
  void setWatchDog(pid_t pid)     { pid_watchdog = pid; }

  // load a .path file
  static void loadPathFile(string name, vector<bool> &buffer);
  static void getKTestFilesInDir(string directoryPath,
                                 vector<string> &results);

  static string getRunTimeLibraryPath(const char *argv0);

  void incTermination(const string &message) override;
  void getTerminationMessages(vector<string> &messages) override;
  unsigned getTerminationCount(const string &message) override;

};

ReplayKleeHandler::ReplayKleeHandler(vector<ExecutionState*> &_results, const string &_md_name)
  : casesGenerated(0),
    indentation(""),
    m_pathsExplored(0),
    pid_watchdog(0),
    outputDirectory(Output),
    results(_results) {

  assert(results.empty());

  // create output directory (if required)
  if (!boost::filesystem::exists(outputDirectory)) {
    boost::system::error_code ec;
    boost::filesystem::create_directories(outputDirectory, ec);
  }

  md_name = boost::filesystem::path(_md_name).stem().string();
//  outs() << "output directory: " << outputDirectory.string() << '\n';
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

#if 0 == 1
  assert(!ReplayTest.empty());
  boost::filesystem::path output = outputDirectory;
  output /= ReplayTest;
  string fname = output.string();
  boost::filesystem::path infile(InputFile);
  boost::replace_all(fname, "test", infile.stem().string());

  ofstream fout(fname);
  if (fout.is_open()) {
    Json::Value root = Json::objectValue;
    // construct the json object representing the results of the test case

    if (state.name == "toarith") {

      const MemoryObject *mo_ptr_v = state.addressSpace.findMemoryObjectByName("*v");
      const MemoryObject *mo_ptr_ptr_v = state.addressSpace.findMemoryObjectByName("**v");

      if (mo_ptr_v != nullptr) {
        const ObjectState *os = state.addressSpace.findObject(mo_ptr_v);
        if (os != nullptr) {
          vector<unsigned char> data;
          os->readConcrete(0, data);
          root["*v"] = toDataString(data);
        }
      }

      if (mo_ptr_ptr_v != nullptr) {
        const ObjectState *os = state.addressSpace.findObject(mo_ptr_ptr_v);
        if (os != nullptr) {
          vector<unsigned char> data;
          os->readConcrete(0, data);
          root["**v"] = toDataString(data);
        }
      }
    } else if (state.name == "set_fields") {

      const MemoryObject *mo_max_range = state.addressSpace.findMemoryObjectByName("max_range_endpoint");
      if (mo_max_range != nullptr) {
        const ObjectState *os = state.addressSpace.findObject(mo_max_range);
        if (os != nullptr) {
          vector<unsigned char> data;
          os->readConcrete(0, data);
          root["max_range_endpoint"] = toDataString(data);
        }
      }
    }

    if (!state.line_trace.empty()) {
      Json::Value &trace = root["trace"] = Json::arrayValue;
      for (const unsigned line : state.line_trace) {
        trace.append(line);
      }
    }

    Json::StreamWriterBuilder builder;
    builder["commentStyle"] = "None";
    builder["indentation"] = indentation;
    unique_ptr<Json::StreamWriter> writer(builder.newStreamWriter());

    writer.get()->write(root, &fout);
    fout << endl;
    fout.flush();
  }
#endif
}

  // load a .path file
void ReplayKleeHandler::loadPathFile(string name, vector<bool> &buffer) {
  ifstream f(name.c_str(), ios::in | ios::binary);

  if (!f.good())
    assert(0 && "unable to open path file");

  while (f.good()) {
    unsigned value;
    f >> value;
    buffer.push_back(!!value);
    f.get();
  }
}

void ReplayKleeHandler::getKTestFilesInDir(string directoryPath,
                                     vector<string> &results) {
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  llvm::error_code ec;
#else
  error_code ec;
#endif
  for (llvm::sys::fs::directory_iterator i(directoryPath, ec), e; i != e && !ec;
       i.increment(ec)) {
    string f = (*i).path();
    if (f.substr(f.size()-6,f.size()) == ".ktest") {
          results.push_back(f);
    }
  }
  if (ec) {
    klee_error("ERROR: unable to read output directory: %s, error=%s", directoryPath.c_str(), ec.message().c_str());
  }
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

bool ReplayKleeHandler::resetWatchDogTimer() const {

  // signal the watchdog process
  if (pid_watchdog != 0) {
    kill(pid_watchdog, SIGUSR1);
    errs() << "BRT-KLEE: " << currentISO8601TimeUTC() << ": txed reset signal\n";
    return true;
  }
  return false;
}

void ReplayKleeHandler::incTermination(const string &message) {
  ++terminationCounters[message];
}

void ReplayKleeHandler::getTerminationMessages(vector<string> &messages) {

  for (const auto &pr : terminationCounters) {
    messages.push_back(pr.first);
  }
}

unsigned ReplayKleeHandler::getTerminationCount(const string &message) {
  return terminationCounters[message];
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

static void interrupt_handle_watchdog() {
  // just wait for the child to finish
}

void load_test_case(Json::Value &root, TestCase &test) {

  // complete test case from json structure
  test.arg_c = root["argC"].asInt();
  test.arg_v = root["argV"].asString();
  test.entry_fn = root["entryFn"].asString();
  test.klee_version = root["kleeRevision"].asString();
  test.lazy_alloc_count = root["lazyAllocationCount"].asUInt();
  test.max_lazy_depth = root["maxLazyDepth"].asUInt();
  test.max_loop_forks = root["maxLoopForks"].asUInt();
  test.max_loop_iter = root["maxLoopIteration"].asUInt();
  test.message = root["message"].asString();
  test.path_condition_vars = root["pathConditionVars"].asString();
  test.status = TestCase::fromStatusString(root["status"].asString());
  test.test_id = root["testID"].asUInt();
  test.start = to_time_point(root["timeStarted"].asString());
  test.stop = to_time_point(root["timeStopped"].asString());

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
      unsigned kind = obj["kind"].asUInt();
      string name = obj["name"].asString();
      string type = obj["type"].asString();
      test.objects.emplace_back(TestObject(addr, count, data, kind, name, type));
    }
  }
}

volatile bool reset_watchdog_timer = false;

static void handle_usr1_signal(int signal, siginfo_t *dont_care, void *dont_care_either) {
  if (signal == SIGUSR1) {
    reset_watchdog_timer = true;
    errs() << "WATCHDOG: " << currentISO8601TimeUTC() << ": rxed reset signal\n";
  }
}

void enumModuleFunctions(const Module *m, set<string> &names) {

  names.clear();
  for (auto itr = m->begin(), end = m->end(); itr != end; ++itr) {
    if (itr->isDeclaration() && !itr->use_empty()) {
      names.insert(itr->getName());
    }
  }
}

int main(int argc, char **argv, char **envp) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();
  exit_code = 0;

  pid_t pid_watchdog = 0;
  if (Watchdog > 0) {

    int pid = fork();
    if (pid < 0) {
      klee_error("unable to fork watchdog");
    } else if (pid > 0) {
      reset_watchdog_timer = false;
      sys::SetInterruptFunction(interrupt_handle_watchdog);

      // catch SIGUSR1
      struct sigaction sa;
      memset(&sa, 0, sizeof(sa));
      sigemptyset(&sa.sa_mask);
      sa.sa_flags = SA_NODEFER;
      sa.sa_sigaction = handle_usr1_signal;
      sigaction(SIGUSR1, &sa, nullptr);

      MonotonicTimer timer;
      const unsigned tid_watchdog = 1;
      timer.set(tid_watchdog, HEARTBEAT_TIMEOUT);

      // Simple stupid code...
      while (true) {
        sleep(1);

        int status;
        int res = waitpid(pid, &status, WNOHANG);

        if (res < 0) {
          if (errno==ECHILD) { // No child, no need to watch but
                               // return error since we didn't catch
                               // the exit.
            errs() << "KLEE: watchdog exiting (no child)\n";
            return 1;
          } else if (errno!=EINTR) {
            perror("watchdog waitpid");
            exit(1);
          }
        } else if (res==pid && WIFEXITED(status)) {
          return WEXITSTATUS(status);
        } else {

          unsigned expired = timer.expired();
          if (reset_watchdog_timer) {

            timer.set(tid_watchdog, HEARTBEAT_TIMEOUT);
            reset_watchdog_timer = false;

          } else if (expired == tid_watchdog) {

            unsigned tries = 0;

            // Ideally this triggers a dump, which may take a while,
            // so try and give the process extra time to clean up.
            while (tries <= 2) {

              tries += 1;
              errs() << "WATCHDOG: " << currentISO8601TimeUTC() << ": timer expired, attempting halt via INT(" << tries << ")\n";
              kill(-pid, SIGINT);

              for (unsigned counter = 0; counter < 30; counter++) {
                sleep(1);
                res = waitpid(pid, &status, WNOHANG);
                if (res < 0) {
                  return 1;
                } else if (res==pid && WIFEXITED(status)) {
                  return WEXITSTATUS(status);
                }
              }
            }

            errs() << "WATCHDOG: " << currentISO8601TimeUTC() << ": kill(9)ing child (I did ask nicely)\n";
            kill(-pid, SIGKILL);
            return 1; // what more can we do
          }
        }
      }
      return 0;
    }
  }

  // create our own process group
  setpgid(0, 0);
  sys::SetInterruptFunction(interrupt_handle);

  if (Watchdog > 0) {
    // then this is the forked child
    pid_watchdog = getppid();
  }

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

  CompareState version1;

  // Load the bytecode...
  // load the bytecode emitted in the generation step...

  // Common setup
  Interpreter::InterpreterOptions IOpts;
  IOpts.mode = Interpreter::ExecModeID::rply;
  IOpts.user_mem_base = (void*) 0x90000000000;
  IOpts.user_mem_size = (0xa0000000000 - 0x90000000000);

  Interpreter::ModuleOptions MOpts;
  MOpts.LibraryDir = "";
  MOpts.Optimize = false;
  MOpts.CheckDivZero = false;
  MOpts.CheckOvershift = false;

  string ErrorMsg;
  LLVMContext ctx;
  llvm::error_code ec;
  vector<ExecutionState*> ex_states;

  // load the first module
  outs() << "Loading: " << InputFile1 << '\n';
  Module *mainModule1 = nullptr;
  OwningPtr<MemoryBuffer> BufferPtr1;

  ec = MemoryBuffer::getFileOrSTDIN(InputFile1.c_str(), BufferPtr1);
  if (ec) {
    klee_error("error loading program '%s': %s", InputFile1.c_str(), ec.message().c_str());
  }

  mainModule1 = getLazyBitcodeModule(BufferPtr1.get(), ctx, &ErrorMsg);

  if (mainModule1) {
    if (mainModule1->MaterializeAllPermanently(&ErrorMsg)) {
      delete mainModule1;
      mainModule1 = nullptr;
    }
  }

  // RLR TODO: verify module is from brt-klee
  if (!mainModule1) klee_error("error loading program '%s': %s", InputFile1.c_str(), ErrorMsg.c_str());

  ReplayKleeHandler *handler1 = new ReplayKleeHandler(ex_states, mainModule1->getModuleIdentifier());
  handler1->setWatchDog(pid_watchdog);

  Interpreter *interpreter1 = Interpreter::createLocal(ctx, IOpts, handler1);
  handler1->setInterpreter(interpreter1);
  const Module *finalModule1 = interpreter1->setModule(mainModule1, MOpts);

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

    mainModule2 = getLazyBitcodeModule(BufferPtr2.get(), ctx, &ErrorMsg);
    if (mainModule2) {
      if (mainModule2->MaterializeAllPermanently(&ErrorMsg)) {
        delete mainModule2;
        mainModule2 = nullptr;
      }
    }

    // RLR TODO: verify module is from brt-klee
    if (!mainModule2) klee_error("error loading program '%s': %s", InputFile2.c_str(), ErrorMsg.c_str());

    ReplayKleeHandler *handler2 = new ReplayKleeHandler(ex_states, mainModule2->getModuleIdentifier());
    handler2->setWatchDog(pid_watchdog);

    Interpreter *interpreter2 = Interpreter::createLocal(ctx, IOpts, handler2);
    handler2->setInterpreter(interpreter2);
    const Module *finalModule2 = interpreter2->setModule(mainModule2, MOpts);

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

  #if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
    // FIXME: This really doesn't look right
    // This is preventing the module from being
    // deleted automatically
    BufferPtr2.take();
  #endif

    if (!CompareExecutions(version1, version2)) {
      outs() << "not the same!\n";
    }
  }

  return exit_code;
}
