//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/TestCase.h"
#include "klee/util/CommonUtil.h"
#include "klee/util/JsonUtil.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"

#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>

#include <string>
#include <iomanip>
#include <iterator>

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
cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"), cl::cat(BrtCategory));
cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"), cl::cat(BrtCategory));
cl::opt<bool> ShowOutput("show-output", cl::desc("display replay's stdout and stderr"), cl::cat(BrtCategory));
cl::opt<bool> ShowTrace("show-trace", cl::desc("display replay's trace"), cl::cat(BrtCategory));
cl::opt<bool> InstrCounters("instr-counters", cl::desc("update test case file with count of instructions executed per function"), cl::cat(BrtCategory));
cl::opt<bool> Verbose("verbose", cl::desc("Display additional information about replay"), cl::cat(BrtCategory));
cl::opt<string> ModuleName("module", cl::desc("override module specified by test case"), cl::cat(BrtCategory));
cl::opt<string> DiffInfo("diff", cl::desc("json formated diff file"), cl::cat(BrtCategory));
cl::opt<string> Prefix("prefix", cl::desc("prefix for loaded test cases"), cl::init("test"), cl::cat(BrtCategory));
cl::opt<unsigned> Timeout("timeout", cl::desc("maximum seconds to replay"), cl::init(10), cl::cat(BrtCategory));
cl::opt<TraceType> TraceT("trace",
  cl::desc("Choose the type of trace (default=marked basic blocks"),
  cl::values(clEnumValN(TraceType::none, "none", "do not trace execution"),
             clEnumValN(TraceType::bblocks, "bblk", "trace execution by basic block"),
             clEnumValN(TraceType::statements, "stmt", "trace execution by source statement"),
             clEnumValN(TraceType::assembly, "assm", "trace execution by assembly line"),
             clEnumValN(TraceType::calls, "calls", "trace execution by function call/return"),
             clEnumValEnd),
  cl::init(TraceType::invalid),
  cl::cat(BrtCategory));
}

map<KModule*,pair<ExecutionState*,uint64_t> > initialized_states;

/***/

class ReplayKleeHandler : public InterpreterHandler {
private:
  vector<pair<ExecutionState*,TerminateReason> > &results;

public:
  ReplayKleeHandler(vector<pair<ExecutionState*,TerminateReason> > &_results, const string &_md_name)
    : InterpreterHandler(Output, _md_name), results(_results) {
    assert(results.empty());
  }

  ~ReplayKleeHandler() override = default;

  void onStateInitialize(ExecutionState &state) override {

    KModule *kmod = interpreter->getKModule();
    if (initialized_states.find(kmod) == initialized_states.end()) {
      initialized_states[kmod] = make_pair(new ExecutionState(state), interpreter->getUsedMemory());
    }
  }

  void onStateFinalize(ExecutionState &state, TerminateReason reason) override  {
    results.push_back(make_pair(new ExecutionState(state), reason));
  }
};

//===----------------------------------------------------------------------===//
// main Driver function
//

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
  if (!result) {
    klee_error("failure materializing program '%s': %s", filename.c_str(), ErrorMsg.c_str());
  }
  BufferPtr.take();
  return result;
}

map<string,KModule*> module_cache;

KModule *PrepareModule(const string &filename, Json::Value &diff_root) {

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
          if (!diff_root.isNull()) applyDiffInfo(diff_root, kmodule);
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

int main(int argc, char *argv[]) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseCmdLineArgs(argc, argv);
  sys::SetInterruptFunction(interrupt_handle);

  exit_code = EXIT_OK;

#ifdef _DEBUG
  EnableMemDebuggingChecks();
#endif // _DEBUG

#ifdef DO_HEAP_PROFILE
  HeapProfilerStart("brt-rply");
#endif

  Json::Value diff_root;
  if (!DiffInfo.empty()) getDiffInfo(DiffInfo, diff_root);

  deque<string> test_files;
  if (ReplayTests.empty()) {
    expandTestFiles(Output, Output, Prefix, test_files);
  } else {
    for (const auto &file : ReplayTests) expandTestFiles(file, Output, Prefix, test_files);
  }
  sort(test_files.begin(), test_files.end());

  for (const string &test_file : test_files) {

    TestCase test;
    ifstream info;
    Json::Value test_root;  // needed here if we intend to update later
    info.open(test_file);
    if (info.is_open()) {
      info >> test_root;

      loadTestCase(test_root, test);
    }
    if (!test.is_ready()) {
      klee_error("failed to load test case '%s'", test_file.c_str());
    }

    outs() << fs::path(test_file).filename().string() << ':' << oflush;
    SetStackTraceContext(test_file);

    string module_name = ModuleName;
    if (module_name.empty()) {
      module_name = test.file_name;
    } else {
      retrieveDiffInfo(diff_root, module_name);
    }

    KModule *kmod = PrepareModule(module_name, diff_root);
    LLVMContext *ctx = kmod->getContextPtr();

    // Common setup
    Interpreter::InterpreterOptions IOpts;
    IOpts.mode = ExecModeID::rply;
    IOpts.user_mem_base = (void *) 0x90000000000;
    IOpts.user_mem_size = (0xa0000000000 - 0x90000000000);
    IOpts.test_case = &test;
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

    // try to re-use an initialized state, if one is available
    auto itr = initialized_states.find(kmod);
    if (itr == initialized_states.end()) {
      interpreter->bindModule(kmod);
    } else {
      interpreter->bindModule(kmod, new ExecutionState(*itr->second.first), itr->second.second);
    }

    theInterpreter = interpreter;
    auto start_time = sys_clock::now();
    interpreter->runFunctionTestCase(test);
    theInterpreter = nullptr;
    auto elapsed = chrono::duration_cast<chrono::milliseconds>(sys_clock::now() - start_time);

    ExecutionState *state = nullptr;

    if (ex_states.empty()) {
      outs() << fs::path(kmod->getModuleIdentifier()).stem().string() << ':';
      outs() << (unsigned) TerminateReason::InternalFault << ':' << 0 << ':' << elapsed.count();
      if (kmod->hasOracle()) {
        outs() << ":" << "did not complete";
      }
      outs() << oendl;
      exit_code = max(exit_code, EXIT_REPLAY_ERROR);
    } else if (ex_states.size() > 1) {
      outs() << fs::path(kmod->getModuleIdentifier()).stem().string() << ':';
      outs() << (unsigned) TerminateReason::InternalFault << ':' << 0 << ':' << elapsed.count();
      if (kmod->hasOracle()) {
        outs() << ":" << "uclibc fault";
      }
      outs() << oendl;
      exit_code = max(exit_code, EXIT_REPLAY_ERROR);
    } else {
      state = ex_states.front().first;
      TerminateReason term_reason = ex_states.front().second;

      assert(state->status == StateStatus::Completed);
      outs() << fs::path(kmod->getModuleIdentifier()).stem().string() << ':';
      outs() << (unsigned) term_reason << ':' << state->reached_target << ':' << elapsed.count();
      if (kmod->hasOracle()) {
        outs() << ':';
        unsigned counter = 0;
        for (const auto &pr : state->o_asserts) {
          if (counter++ != 0) outs() << ',';
          outs() << pr.first;
        }
      }
      outs() << oendf;

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
          outs() << "#stdout: " << toDataString(stdout_capture, 64) << '\n';
          for (auto itr = stdout_capture.begin(), end = stdout_capture.end(); itr != end; ++itr) {
            outs() << *itr;
          }
        }

        vector<unsigned char> stderr_capture;
        state->stderr_capture.get_data(stderr_capture);
        if (!stderr_capture.empty()) {
          outs() << "#stderr: " << toDataString(stderr_capture, 64) << '\n';
          for (auto itr = stderr_capture.begin(), end = stderr_capture.end(); itr != end; ++itr) {
            outs() << *itr;
          }
        }
      }

      if (ShowTrace) {
        outs() << "#trace:" << oendl;
        for (const auto &entry : state->trace) {
          outs() << to_string(entry) << oendl;
        }
      }

      if (auto *counters = IOpts.fn_instr_counters) {
        outs() << "#instr counters:" << oendl;
        for (const auto &pr : *counters) {
          outs() <<  pr.first->getName() << ':' << pr.second;
        }
        counters->clear();
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
  module_cache.clear();

  return exit_code;
}
