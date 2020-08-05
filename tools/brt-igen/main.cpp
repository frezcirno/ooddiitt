//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Interpreter.h"
#include "klee/Statistics.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Config/CompileTimeInfo.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/System/Memory.h"
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
#include "klee/util/CommonUtil.h"
#include "klee/util/JsonUtil.h"

#include <openssl/sha.h>

#ifdef _DEBUG
#include <gperftools/tcmalloc.h>
#include <gperftools/heap-profiler.h>
#include <gperftools/heap-checker.h>
#endif


#include "llvm/Support/system_error.h"
#include "json/json.h"
#include <signal.h>
#include <unistd.h>
#include <sys/wait.h>

#include <cerrno>
#include <string>
#include <iomanip>
#include <sstream>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include <regex>

using namespace llvm;
using namespace klee;
using namespace std;
namespace fs=boost::filesystem;

namespace {
cl::OptionCategory BrtCategory("specific brt options");
cl::opt<string> InputFile(cl::desc("<input bytecode>"), cl::Positional, cl::init("-"));
cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::cat(BrtCategory));
cl::opt<string> EntryPoint("entry-point", cl::desc("Start local symbolic execution at entry-point"), cl::cat(BrtCategory));
cl::opt<string> UserMain("user-main", cl::desc("Consider the function with the given name as the main point"), cl::init("main"), cl::cat(BrtCategory));
cl::opt<string> Progression("progression", cl::desc("progressive phases of unconstraint (default=e:60)"), cl::cat(BrtCategory));
cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
cl::list<string> InputArgv(cl::ConsumeAfter, cl::desc("<program arguments>..."));
cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
cl::opt<bool> AllOutput("all-output", cl::desc("Generate all test files (reaching or not)"));
cl::opt<bool> VerifyConstraints("verify-constraints", cl::desc("Perform additional constraint verification"), cl::cat(BrtCategory));
cl::opt<bool> Verbose("verbose", cl::init(false), cl::desc("Emit verbose output"), cl::cat(BrtCategory));
cl::opt<string> DiffInfo("diff", cl::desc("json formatted diff file"), cl::cat(BrtCategory));
cl::opt<TraceType> TraceT("trace",
  cl::desc("Choose the type of trace (default=marked basic blocks"),
  cl::values(clEnumValN(TraceType::none, "none", "do not trace execution"),
             clEnumValN(TraceType::bblocks, "bblk", "trace execution by basic block"),
             clEnumValN(TraceType::statements, "stmt", "trace execution by source statement"),
             clEnumValN(TraceType::assembly, "assm", "trace execution by assembly line"),
             clEnumValEnd),
  cl::init(TraceType::invalid),
  cl::cat(BrtCategory));

#if 0 == 1
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<bool> WriteCVCs("write-cvcs", cl::desc("Write .cvc files for each test case"));
  cl::opt<bool> WriteKQueries("write-kqueries", cl::desc("Write .kquery files for each test case"));
  cl::opt<bool> WriteSMT2s("write-smt2s", cl::desc("Write .smt2 (SMT-LIBv2) files for each test case"));
  cl::opt<bool> WriteCov("write-cov", cl::desc("Write coverage information for each test case"));
  cl::opt<bool> WriteTestInfo("write-test-info", cl::desc("Write additional test case information"));
  cl::opt<bool> WritePaths("write-paths", cl::desc("Write .path files for each test case"));
  cl::opt<bool> WriteSymPaths("write-sym-paths", cl::desc("Write .sym.path files for each test case"));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));

cl::opt<bool> WithPOSIXRuntime("posix-runtime",
  cl::desc("Link with POSIX runtime.  Options that can be passed as arguments to the programs are: --sym-arg <max-len>  --sym-args <min-argvs> <max-argvs> <max-len> + file model options")
  );
cl::opt<unsigned> MakeConcreteSymbolic("make-concrete-symbolic",
  cl::desc("Probabilistic rate at which to make concrete reads symbolic, "
           "i.e. approximately 1 in n concrete reads will be made symbolic (0=off, 1=all).  "
           "Used for testing."),
  cl::init(0));

#endif
cl::opt<bool> UnconstrainConstGlobals("unconstrain-const-globals", cl::desc("include constants in global unconstrained state"), cl::cat(BrtCategory));
cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"), cl::cat(BrtCategory));
cl::opt<unsigned> Watchdog("watchdog", cl::desc("Use a watchdog process to monitor se. (default = 0 secs. if activated, suggest 300"), cl::init(0), cl::cat(BrtCategory));
cl::opt<string> Prefix("prefix", cl::desc("prefix for emitted test cases"), cl::init("test"), cl::cat(BrtCategory));
cl::opt<unsigned> Job("job", cl::desc("appended to test case prefix"), cl::init(UINT_MAX), cl::cat(BrtCategory));
cl::opt<bool> ShowArgs("show-args", cl::desc("show invocation command line args"), cl::cat(BrtCategory));
}

/***/

class InputGenKleeHandler : public InterpreterHandler {
private:
  unsigned casesGenerated;
  unsigned nextTestCaseID;
  string indentation;
  unsigned m_pathsExplored; // number of paths explored so far
  pid_t pid_watchdog;

  // used for writing .ktest files
  const vector<string> &args;
  map<TerminateReason,unsigned> terminationCounters;
  sys_clock::time_point started_at;

public:
  InputGenKleeHandler(const vector<string> &args, const string &_md_name, const string &_prefix);
  ~InputGenKleeHandler() override = default;

  unsigned getNumTestCases() const override { return casesGenerated; }
  unsigned getNumPathsExplored() { return m_pathsExplored; }
  void incPathsExplored() override { m_pathsExplored++; }

  void processTestCase(ExecutionState  &state, TerminateReason term_reason) override;
  bool resetWatchDogTimer() const override;
  void setWatchDog(pid_t pid)     { pid_watchdog = pid; }

  void getTerminationMessages(vector<TerminateReason> &reasons) override;
  unsigned getTerminationCount(TerminateReason reason) override;
};

InputGenKleeHandler::InputGenKleeHandler(const vector<string> &_args, const string &_md_name, const string &_prefix)
  : InterpreterHandler(Output, _md_name, _prefix),
    casesGenerated(0),
    nextTestCaseID(0),
    indentation(""),
    m_pathsExplored(0),
    pid_watchdog(0),
    args(_args) {

  started_at = sys_clock::now();

  // if the directory was not newly created, then we need to find the next available case id
  if (!wasOutputCreated()) {

    // find the next available test id
    bool done = false;
    while (!done) {

      // find the next missing test case id.
      boost::filesystem::path filename(getOutputFilename(getTestFilename("json", nextTestCaseID)));
      if (boost::filesystem::exists(filename)) {
        ++nextTestCaseID;
      } else {
        done = true;
      }
    }
  }
  if (IndentJson) indentation = "  ";
}

/* Outputs all files (.ktest, .kquery, .cov etc.) describing a test case */
void InputGenKleeHandler::processTestCase(ExecutionState &state, TerminateReason term_reason) {

  Interpreter *i = getInterpreter();
  assert(i != nullptr);
  assert(!state.isProcessed);

  if (!NoOutput && (AllOutput || state.reached_target || term_reason == TerminateReason::Timeout)) {

    // select the next test id for this function
    unsigned testID = nextTestCaseID++;
    const char *ext = nullptr;
    if (term_reason == TerminateReason::Timeout) ext = "dump";

    ofstream fout;
    if (openTestCaseFile(fout, testID, ext)) {

      auto stopped_at = sys_clock::now();

      // construct the json object representing the test case
      Json::Value root = Json::objectValue;
      root["module"] = getModuleName();
      root["file"] = getFileName();
      root["entryFn"] = state.name;
      root["testID"] = testID;
      root["argC"] = args.size();
      root["lazyAllocationCount"] = state.lazyAllocationCount;
      root["lazyStringLength"] = state.lazyStringLength;
      root["maxLazyDepth"] = state.maxLazyDepth;
      root["maxStatesInLoop"] = state.maxStatesInLoop;
      root["timeStarted"] = klee::to_string(started_at);
      root["timeStopped"] = klee::to_string(stopped_at);
      root["timeElapsed"] = chrono::duration_cast<chrono::milliseconds>(stopped_at - started_at).count();

      const UnconstraintFlagsT *flags = i->getUnconstraintFlags();
      if (flags != nullptr) {
        root["unconstraintFlags"] = flags->to_string();
        root["unconstraintDescription"] = klee::to_string(*flags);
      }
      root["kleeRevision"] = KLEE_BUILD_REVISION;
      root["termination"] = (unsigned) term_reason;
      if (state.instFaulting != nullptr) {
        root["instFaulting"] = state.instFaulting->info->assemblyLine;
      }

      Json::Value &msgs = root["messages"] = Json::arrayValue;
      for (auto msg : state.messages) {
        msgs.append(msg);
      }

      // store the path condition
      string constraints;
      i->getConstraintLog(state, constraints, LogType::SMTVARS);
      root["pathConditionVars"] = constraints;

      {
        stringstream ss;
        for (unsigned index = 0; index < args.size(); ++index) {
          if (index > 0)
            ss << ' ';
          ss << '\'' << args[index] << '\'';
        }
        root["argV"] = ss.str();
      }

      vector<ExprSolution> args;
      for (auto itr = state.arguments.begin(), end = state.arguments.end(); itr != end; ++itr) {
        args.emplace_back(make_pair(*itr, nullptr));
      }

      vector<SymbolicSolution> out;
      if (!i->getSymbolicSolution(state, out, args)) {
        klee_warning("unable to get symbolic solution, losing test case");
      }
      Json::Value &objects = root["objects"] = Json::arrayValue;
      for (auto itrObj = out.begin(), endObj = out.end(); itrObj != endObj; ++itrObj) {

        auto &test = *itrObj;
        const MemoryObject *mo = test.first;
        vector<unsigned char> &data = test.second;

        if (mo->name == "#stdin_buff") {
          root["stdin"] = toDataString(data, state.stdin_offset);
        } else {

          Json::Value obj = Json::objectValue;

          // the program arguments argv_d..d require truncating at null terminator
          // otherwise, risk missing oob access
          regex re("argv_[0-9]+");
          if (regex_match(mo->name, re)) {
            // set new count at null terminator
            auto itr = find(data.begin(), data.end(), 0);
            assert(itr != data.end());  // if not null-terminated, then we're not in kansas anymore
            unsigned len = distance(data.begin(), itr) + 1;
            obj["count"] = len;
            assert(mo->type->isArrayTy()); // and your little dog too...
            obj["type"] = klee::to_string(ArrayType::get(mo->type->getArrayElementType(), len));
            obj["data"] = toDataString(data, len);
          } else {
            obj["count"] = mo->count;
            obj["type"] = klee::to_string(mo->type);
            obj["data"] = toDataString(data);
          }
          obj["name"] = mo->name;
          obj["kind"] = (unsigned) mo->kind;

          // scale to 32 or 64 bits
          unsigned ptr_width = (Context::get().getPointerWidth() / 8);
          vector<unsigned char> addr;
          unsigned char *addrBytes = ((unsigned char *) &(test.first->address));
          for (unsigned index = 0; index < ptr_width; ++index, ++addrBytes) {
            addr.push_back(*addrBytes);
          }
          obj["addr"] = toDataString(addr);
          obj["align"] = mo->align;

          objects.append(obj);
        }
      }

      Json::Value &arguments = root["arguments"] = Json::arrayValue;
      for (auto itr = args.begin(), end = args.end(); itr != end; ++itr) {
        klee::ref<klee::ConstantExpr> ce = itr->second;
        if (ce.isNull()) {
          arguments.append("");
        } else {
          uint64_t value = ce->getZExtValue();
          unsigned width = ce->getWidth() / 8;
          if (width == 0) width = 1;
          unsigned char *byte = ((unsigned char *) &value);
          vector<unsigned char> v;
          for (unsigned idx = 0; idx < width; ++idx) {
            v.push_back(*byte++);
          }
          arguments.append(toDataString(v));
        }
      }

      TraceType trace_type = i->getTraceType();
      if (trace_type != TraceType::invalid) {
        root["traceType"] = (unsigned)trace_type;
        Json::Value &trace = root["trace"] = Json::arrayValue;
        for (const auto &entry : state.trace) {
          trace.append(to_string(entry));
        }
      }

      // write the constructed json object to file
      Json::StreamWriterBuilder builder;
      builder["commentStyle"] = "None";
      builder["indentation"] = indentation;
      unique_ptr<Json::StreamWriter> writer(builder.newStreamWriter());

      writer.get()->write(root, &fout);
      fout << endl;
      state.isProcessed = true;
      ++casesGenerated;
    } else {
      klee_warning("unable to write output test case, losing it");
    }
  }
}

bool InputGenKleeHandler::resetWatchDogTimer() const {

  // signal the watchdog process
  if (pid_watchdog != 0) {
    kill(pid_watchdog, SIGUSR1);
    errs() << "brt-igen: " << currentISO8601TimeUTC() << ": txed reset signal\n";
    return true;
  }
  return false;
}

void InputGenKleeHandler::getTerminationMessages(vector<TerminateReason> &reasons) {

  for (const auto &pr : terminationCounters) {
    reasons.push_back(pr.first);
  }
}

unsigned InputGenKleeHandler::getTerminationCount(TerminateReason reason) {
  return terminationCounters[reason];
}

//===----------------------------------------------------------------------===//
// main Driver function
//

static void parseArguments(int argc, char **argv) {
  cl::SetVersionPrinter(klee::printVersion);
  cl::ParseCommandLineOptions(argc, argv, " klee\n");
}

#if 0 == 1
static int initEnv(Module *mainModule) {

  /*
    nArgcP = alloc oldArgc->getType()
    nArgvV = alloc oldArgv->getType()
    store oldArgc nArgcP
    store oldArgv nArgvP
    klee_init_environment(nArgcP, nArgvP)
    nArgc = load nArgcP
    nArgv = load nArgvP
    oldArgc->replaceAllUsesWith(nArgc)
    oldArgv->replaceAllUsesWith(nArgv)
  */

  Function *mainFn = mainModule->getFunction(UserMain);
  if (!mainFn) {
    klee_error("'%s' function not found in module.", UserMain.c_str());
  }

  if (mainFn->arg_size() < 2) {
    klee_error("Cannot handle ""--posix-runtime"" when main() has less than two arguments.\n");
  }

  Instruction *firstInst = static_cast<Instruction *>(mainFn->begin()->begin());

  Value *oldArgc = static_cast<Argument *>(mainFn->arg_begin());
  Value *oldArgv = static_cast<Argument *>(++mainFn->arg_begin());

  AllocaInst* argcPtr = new AllocaInst(oldArgc->getType(), "argcPtr", firstInst);
  AllocaInst* argvPtr = new AllocaInst(oldArgv->getType(), "argvPtr", firstInst);

  /* Insert void klee_init_env(int* argc, char*** argv) */
  vector<const Type*> params;
  LLVMContext &ctx = mainModule->getContext();
  params.push_back(Type::getInt32Ty(ctx));
  params.push_back(Type::getInt32Ty(ctx));
  Function* initEnvFn = cast<Function>(mainModule->getOrInsertFunction("klee_init_env",
                                                                       Type::getVoidTy(ctx),
                                                                       argcPtr->getType(),
                                                                       argvPtr->getType(),
                                                                       NULL));
  assert(initEnvFn);
  vector<Value*> args;
  args.push_back(argcPtr);
  args.push_back(argvPtr);
  Instruction* initEnvCall = CallInst::Create(initEnvFn, args,
                                              "", firstInst);
  Value *argc = new LoadInst(argcPtr, "newArgc", firstInst);
  Value *argv = new LoadInst(argvPtr, "newArgv", firstInst);

  oldArgc->replaceAllUsesWith(argc);
  oldArgv->replaceAllUsesWith(argv);

  new StoreInst(oldArgc, argcPtr, initEnvCall);
  new StoreInst(oldArgv, argvPtr, initEnvCall);

  return 0;
}
#endif

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

volatile bool reset_watchdog_timer = false;

static void handle_usr1_signal(int signal, siginfo_t *dont_care, void *dont_care_either) {
  UNUSED(dont_care);
  UNUSED(dont_care_either);
  if (signal == SIGUSR1) {
    reset_watchdog_timer = true;
    errs() << "WATCHDOG: " << currentISO8601TimeUTC() << ": rxed reset signal\n";
  }
}

bool parseUnconstraintProgression(vector<Interpreter::ProgressionDesc> &progression, const string &str) {

  bool result = false;
  if (str.empty()) {
    // default progression
    UnconstraintFlagsT flags;
    flags.setUnconstrainExterns();
    progression.emplace_back(60, flags);
    result = true;
  } else {

    // parse out the progression phases
    vector<string> phases;
    boost::split(phases, str, [](char c){return c == ',';});
    for (const auto &phase: phases) {

      // loop through each phase in progression
      UnconstraintFlagsT flags;
      unsigned timeout = 60;

      // parse out the phase
      bool done = false;
      for (auto itr = phase.begin(), end = phase.end(); (!done) && itr != end; ++itr) {

        if (*itr == ':') {
          // rest of string is a unsigned timeout
          timeout = (unsigned) stoi(string(itr + 1, end));
          char suffix = (char) tolower(phase.back());
          if (suffix == 'm') {
            timeout *= 60;
          } else if (suffix == 'h') {
            timeout *= (60 * 60);
          }
          done = true;
        } else if (*itr == 'e') {
          flags.set(UNCONSTRAIN_EXTERN_FLAG);
        } else if (*itr == 'g') {
          flags.set(UNCONSTRAIN_GLOBAL_FLAG);
        } else if (*itr == 's') {
          flags.set(UNCONSTRAIN_STUB_FLAG);
        } else if (*itr != 'i') {
          // invalid character
          return false;
        }
      }
      progression.emplace_back(timeout, flags);
    }
    result = (phases.size() == progression.size());
  }
  return result;
}

bool getDiffInfo(const string &diff_file, Json::Value &root) {

  bool result = false;
  string filename = diff_file;
  if (!fs::exists(fs::path(filename))) {
    filename = (fs::path(Output) / filename).string();
  }

  ifstream infile(filename);
  if (infile.is_open()) {
    infile >> root;
    result = true;
  } else {
    klee_error("failed opening diff file: %s", filename.c_str());
  }
  return result;
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
  if (!result) klee_error("failure materializing program '%s': %s", filename.c_str(), ErrorMsg.c_str());
  BufferPtr.take();
  return result;
}

KModule *PrepareModule(const string &filename, Json::Value &diff_root) {

  if (Module *module = LoadModule(filename)) {
    if (!isPrepared(module)) {
      klee_error("not prepared: %s", module->getModuleIdentifier().c_str());
    } else {

      if (KModule *kmodule = new KModule(module)) {
        kmodule->prepare();
        if (!diff_root.isNull()) applyDiffInfo(diff_root, kmodule);
        return kmodule;
      }
    }
  }
  return nullptr;
}

int main(int argc, char *argv[]) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();
  sys::SetInterruptFunction(interrupt_handle);
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
      timer.set(tid_watchdog, Watchdog);

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

            timer.set(tid_watchdog, Watchdog);
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
  if (ShowArgs) show_args(argc, argv);

#ifdef _DEBUG
  EnableMemDebuggingChecks();
#endif // _DEBUG

  Json::Value diff_root;
  if (!DiffInfo.empty()) getDiffInfo(DiffInfo, diff_root);

  // select the module file and entry point
  string module_file = InputFile;
  string entry_point = EntryPoint;
  translateDifftoModule(diff_root, module_file, entry_point);

  // Load the bytecode and verify that its been prepped
  KModule *kmod = PrepareModule(module_file, diff_root);
  assert(kmod != nullptr);

  LLVMContext *ctx = kmod->getContextPtr();

#if 0 == 1
  if (WithPOSIXRuntime) {
    SmallString<128> Path(LibraryDir);

    string posixLib = "libkleeRuntimePOSIX";
    Module::PointerSize width = mainModule->getPointerSize();
    if (width == Module::PointerSize::Pointer32) {
      posixLib += "-32";
    } else if (width == Module::PointerSize::Pointer64) {
      posixLib += "-64";
    }
    posixLib += ".bca";

    llvm::sys::path::append(Path, posixLib);
    outs() << "NOTE: Using model: " << Path.c_str() << '\n';
    mainModule = klee::linkWithLibrary(mainModule, Path.c_str());
    assert(mainModule && "unable to link with simple model");
  }
#endif
  // Get the desired main function.  klee_main initializes uClibc
  // locale and other data and then calls main.
  Function *mainFn = kmod->getFunction(UserMain);

  vector<string> args;
  args.reserve(InputArgv.size() + 1);
  args.push_back(module_file);
  args.insert(args.end(), InputArgv.begin(), InputArgv.end());

  string prefix = Prefix;
  if (Job != UINT_MAX) {
    ostringstream ss;
    ss << prefix << '-' << std::setfill('0') << std::setw(5) << Job;
    prefix = ss.str();
  }
  InputGenKleeHandler *handler = new InputGenKleeHandler(args, kmod->getModuleIdentifier(), prefix);
  handler->setWatchDog(pid_watchdog);

  Interpreter::InterpreterOptions IOpts;
  if (!parseUnconstraintProgression(IOpts.progression, Progression)) {
    klee_error("failed to parse unconstraint progression: %s", Progression.c_str());
  }
  IOpts.mode = ExecModeID::igen;
  IOpts.userMain = mainFn;
  IOpts.user_mem_base = (void*) 0x80000000000;
  IOpts.user_mem_size = (0x90000000000 - 0x80000000000);
  IOpts.verbose = Verbose;
  IOpts.verify_constraints = VerifyConstraints;
  if (TraceT != TraceType::invalid) {
    IOpts.trace = TraceT;
  }

  theInterpreter = Interpreter::createLocal(*ctx, IOpts, handler);
  handler->setInterpreter(theInterpreter);
  theInterpreter->bindModule(kmod);

  auto start_time = sys_clock::now();
  outs() << "Started: " << to_string(start_time) << '\n';
  outs().flush();

  // select program entry point
  Function *entryFn = mainFn;
  if (!entry_point.empty()) {
    entryFn = kmod->getFunction(entry_point);
    if (entryFn == nullptr) {
      klee_error("Unable to find function: %s", entry_point.c_str());
    }
  }
  if (entryFn != nullptr) {
    theInterpreter->runFunctionUnconstrained(entryFn);
  }

  auto finish_time = sys_clock::now();
  outs() << "Finished: " << to_string(finish_time) << '\n';
  auto elapsed = chrono::duration_cast<chrono::seconds>(finish_time - start_time);
  outs() << "Elapsed: " << elapsed.count() << '\n';

  vector<TerminateReason> termination_reasons;
  handler->getTerminationMessages(termination_reasons);
  for (const auto &reason : termination_reasons) {
    outs() << "brt-igen: term: " << to_string(reason) << ": " << handler->getTerminationCount(reason) << '\n';
  }

  uint64_t queries = *theStatisticManager->getStatisticByName("Queries");
  uint64_t queriesValid = *theStatisticManager->getStatisticByName("QueriesValid");
  uint64_t queriesInvalid = *theStatisticManager->getStatisticByName("QueriesInvalid");
  uint64_t queryCounterexamples = *theStatisticManager->getStatisticByName("QueriesCEX");
  uint64_t queryConstructs = *theStatisticManager->getStatisticByName("QueriesConstructs");
  uint64_t instructions = *theStatisticManager->getStatisticByName("Instructions");
  uint64_t forks = *theStatisticManager->getStatisticByName("Forks");

  outs() << "brt-igen: done: explored paths = " << 1 + forks << "\n";

  // Write some extra information in the info file which users won't
  // necessarily care about or understand.
  if (queries) {
    outs() << "brt-igen: done: avg. constructs per query = " << queryConstructs / queries << "\n";
  }
  outs()
    << "brt-igen: done: total queries = " << queries << "\n"
    << "brt-igen: done: valid queries = " << queriesValid << "\n"
    << "brt-igen: done: invalid queries = " << queriesInvalid << "\n"
    << "brt-igen: done: query cex = " << queryCounterexamples << "\n";

  outs() << "brt-igen: done: total instructions = " << instructions << "\n";
  outs() << "brt-igen: done: completed paths = " << handler->getNumPathsExplored() << "\n";
  outs() << "brt-igen: done: generated tests = " << handler->getNumTestCases() << "\n";

  delete theInterpreter;
  delete handler;
  delete kmod;
  delete ctx;

  return exit_code;
}
