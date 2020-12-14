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
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include <klee/Internal/Support/ModuleUtil.h>
#include "json/json.h"
#include "klee/TestCase.h"
#include "klee/util/CommonUtil.h"
#include "klee/util/JsonUtil.h"
#include "StateComparison.h"

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
cl::OptionCategory BrtCategory("specific brt options");
cl::list<string> ReplayTests(cl::desc("<test case to replay>"), cl::Positional, cl::ZeroOrMore);
cl::opt<string> PrevModule("prev", cl::desc("<prev-bytecode> (default=@prev)"), cl::init("@prev"), cl::cat(BrtCategory));
cl::opt<string> PostModule("post", cl::desc("<post-bytecode> (default=@post)"), cl::init("@orcl,post"), cl::cat(BrtCategory));
cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));
cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"), cl::cat(BrtCategory));
cl::opt<string> Prefix("prefix", cl::desc("prefix for loaded test cases"), cl::init("test"), cl::cat(BrtCategory));
cl::opt<string> DiffInfo("diff", cl::desc("json formatted diff file"), cl::cat(BrtCategory));
cl::opt<unsigned> Timeout("timeout", cl::desc("maximum seconds to replay"), cl::init(10), cl::cat(BrtCategory));
cl::opt<unsigned> MaxFnSnapshots("max-fn-snapshots",
                                 cl::desc("maximum number of snapshots taken returning from any single function (default=500"),
                                 cl::init(500), cl::cat(BrtCategory));
cl::opt<bool> ShowArgs("show-args", cl::desc("show invocation command line args"), cl::cat(BrtCategory));
}

/***/

map<KModule*,pair<ExecutionState*,uint64_t> > initialized_states;

class ICmpKleeHandler : public InterpreterHandler {
private:
  StateVersion &ver;
  map<KFunction *, unsigned> snapshot_counters;

public:
  explicit ICmpKleeHandler(StateVersion &_ver) : InterpreterHandler(Output, _ver.kmodule->getModuleIdentifier()), ver(_ver) { }
  ~ICmpKleeHandler() override = default;

  void onStateInitialize(ExecutionState &state) override {
    ver.initialState = new ExecutionState(state);
    getInterpreter()->getGlobalVariableMap(ver.global_map);

    // save a copy of the uclibc initialized state
    // only add if not already cached.  find first to avoid creating new state if not to be saved.
    if (initialized_states.find(ver.kmodule) == initialized_states.end()) {
      initialized_states.insert(make_pair(ver.kmodule, make_pair(new ExecutionState(state), interpreter->getUsedMemory())));
    }
  }

  void onStateFinalize(ExecutionState &state, TerminateReason reason) override {
    if (ver.finalState == nullptr) {
      ver.finalState = new ExecutionState(state);
      ver.term_reason = reason;
    } else {
      ver.forked = true;
    }
  }

  void onStateUserFunctionReturn(ExecutionState &state) override {
    assert(!state.stack.empty());
    KFunction *returning = state.stack.back().kf;
    if (!(returning->isDiffAdded() || returning->isDiffRemoved())) {
      unsigned &counter = snapshot_counters[returning];
      if (MaxFnSnapshots == 0 || counter++ < MaxFnSnapshots) {
        ver.fn_returns.emplace_back(make_pair(returning, new ExecutionState(state)));
      }
    }
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

KModule *PrepareModule(const string &filename) {

  if (Module *module = LoadModule(filename)) {
    if (!isPrepared(module)) {
      klee_error("not prepared: %s", module->getModuleIdentifier().c_str());
    } else {
      if (KModule *kmodule = new KModule(module)) {
        kmodule->prepare();
        return kmodule;
      }
    }
  }
  return nullptr;
}

#define EXIT_OK               0
#define EXIT_REPLAY_ERROR     1
#define EXIT_STATUS_CONFLICT  2
#define EXIT_TRACE_CONFLICT   3

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

static const char *err_context = nullptr;
static void PrintStackTraceSignalHandler(void *) {
  if (err_context != nullptr) {
    fprintf(stderr, "context: %s\n", err_context);
  }
  sys::PrintStackTrace(stderr);
}

int main(int argc, char *argv[]) {

#ifdef _DEBUG
  EnableMemDebuggingChecks();
#endif // _DEBUG

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::AddSignalHandler(PrintStackTraceSignalHandler, nullptr);
  sys::SetInterruptFunction(interrupt_handle);

  // write out command line info, for reference
  if (ShowArgs) show_args(argc, argv);

  exit_code = 0;

  Json::Value diff_root;
  getDiffInfo(DiffInfo, diff_root);

  string mod_name1 = PrevModule;
  retrieveDiffInfo(diff_root, mod_name1);

  string mod_name2 = PostModule;
  retrieveDiffInfo(diff_root, mod_name2);

  // Load the bytecode...
  // load the bytecode emitted in the generation step...
  KModule *kmod1 = PrepareModule(mod_name1);
  if (kmod1 == nullptr) {
    klee_error("failed to load %s", mod_name1.c_str());
  }
  KModule *kmod2 = PrepareModule(mod_name2);
  if (kmod2 == nullptr) {
    klee_error("failed to load %s", mod_name2.c_str());
  }

  if (!diff_root.isNull()) {
    applyDiffInfo(diff_root, kmod1);
    applyDiffInfo(diff_root, kmod2);
  }

  LLVMContext *ctx1 = kmod1->getContextPtr();
  LLVMContext *ctx2 = kmod2->getContextPtr();

  deque<string> test_files;
  if (ReplayTests.empty()) {
    expandTestFiles(Output, Output, Prefix, test_files);
  } else {
    for (auto file : ReplayTests) expandTestFiles(file, Output, Prefix, test_files);
  }
  sort(test_files.begin(), test_files.end());

  if (!kmod2->hasOracle()) {
    klee_warning("%s does not contain an oracle", kmod2->getModuleIdentifier().c_str());
  }

#ifdef DO_HEAP_PROFILE
  HeapProfilerStart("brt-icmp");
  HeapProfilerDump("pre-loop");
#endif

  for (const string &test_file : test_files) {

    TestCase test;
    ifstream info;
    info.open(test_file);
    if (info.is_open()) {
      Json::Value root;  // needed here if we intend to update later
      info >> root;
      loadTestCase(root, test);
    }
    if (!test.is_ready()) {
      klee_error("failed to load test case '%s'", test_file.c_str());
    }

    // Common setup
    Interpreter::InterpreterOptions IOpts;
    IOpts.mode = ExecModeID::rply;
    IOpts.user_mem_base = (void *) 0x90000000000;
    IOpts.user_mem_size = (0xa0000000000 - 0x90000000000);
    IOpts.test_case = &test;
    IOpts.trace = test.trace_type;
    UnconstraintFlagsT flags;
    IOpts.progression.emplace_back(Timeout, flags);

    StateVersion version1(kmod1);
    StateVersion version2(kmod2);

    auto *handler1 = new ICmpKleeHandler(version1);
    Interpreter *interpreter1 = Interpreter::createLocal(*ctx1, IOpts, handler1);
    handler1->setInterpreter(interpreter1);

    // try to re-use an initialized state, if one is available
    auto itr1 = initialized_states.find(kmod1);
    if (itr1 == initialized_states.end()) {
      interpreter1->bindModule(kmod1);
    } else {
      interpreter1->bindModule(kmod1, new ExecutionState(*itr1->second.first), itr1->second.second);
    }

    theInterpreter = interpreter1;
    interpreter1->runFunctionTestCase(test);
    theInterpreter = nullptr;

    if (version1.finalState != nullptr && version1.finalState->status == StateStatus::Completed) {

      string filename = fs::path(test_file).filename().string();
      outs() << filename << ';' << oflush;
      err_context = test_file.c_str();

      // now, lets do it all again with the second module
      auto *handler2 = new ICmpKleeHandler(version2);
      Interpreter *interpreter2 = Interpreter::createLocal(*ctx2, IOpts, handler2);
      handler2->setInterpreter(interpreter2);

      // try to re-use an initialized state, if one is available
      auto itr2 = initialized_states.find(kmod2);
      if (itr2 == initialized_states.end()) {
        interpreter2->bindModule(kmod2);
      } else {
        interpreter2->bindModule(kmod2, new ExecutionState(*itr2->second.first), itr2->second.second);
      }

      theInterpreter = interpreter2;
      interpreter2->runFunctionTestCase(test);
      theInterpreter = nullptr;

      StateComparator cmp(filename, test, version1, version2);
      const KInstruction *ki =  cmp.checkTermination();
      if (ki == nullptr) {
        if (cmp.isEquivalent()) {
          outs() << "equivalent;0;";
          outs() << to_string(cmp.oracle_ids);
          outs() << oendl;
        } else {
          outs() << "divergent;" << cmp.checkpoints.size() << ';';
          outs() << to_string(cmp.oracle_ids);
          outs() << oendl;
          for (const auto &cp : cmp.checkpoints) {
            if (!cp.diffs.empty()) {
              outs().indent(2) << to_string(cp) << oendl;
              for (const auto &diff : cp.diffs) {
                outs().indent(4) << to_string(diff) << oendl;
              }
            }
          }
        }
      } else outs() << "diff (termination)" << " L" << ki->info->assemblyLine <<" (" << ki->info->file << ':' << ki->info->line << ')' << oendl;
      delete interpreter2;
      delete handler2;
    } else {
      outs() << fs::path(test_file).filename().string() << ": " << "version1 timeout" << oendf;
    }
    delete interpreter1;
    delete handler1;

#ifdef DO_HEAP_PROFILE
//      HeapProfilerDump("end-loop");
#endif
  }

#ifdef DO_HEAP_PROFILE
//  HeapProfilerDump("post-loop");
#endif

  // clean up the loaded modules
  delete kmod1;
  delete ctx1;
  delete kmod2;
  delete ctx2;

#ifdef DO_HEAP_PROFILE
  HeapProfilerDump("going home");
  HeapProfilerStop();
#endif

#ifdef _DEBUG
  DisableMemDebuggingChecks();
#endif // _DEBUG

  return exit_code;
}
