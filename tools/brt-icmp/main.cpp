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
  cl::list<string> ReplayTests(cl::desc("<test case to replay>"), cl::Positional, cl::ZeroOrMore);
  cl::opt<string> PreModule("pre", cl::desc("<pre-bytecode>"));
  cl::opt<string> PostModule("post", cl::desc("<post-bytecode2>"));
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
  cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));
  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"));
  cl::opt<string> Prefix("prefix", cl::desc("prefix for loaded test cases"), cl::init("test"));
  cl::opt<string> DiffInfo("diff-info", cl::desc("json formated diff file"));
  cl::opt<string> BlackLists("cmp-blacklists", cl::desc("functions and type of skip value comparison"), cl::init("blacklists.json"));
  cl::opt<unsigned> Timeout("timeout", cl::desc("maximum seconds to replay"), cl::init(12));
  cl::opt<bool> ShowArgs("show-args", cl::desc("show invocation command line args"));
}

/***/

class ICmpKleeHandler : public InterpreterHandler {
private:
  string indentation;
  StateVersion &ver;

public:
  explicit ICmpKleeHandler(StateVersion &_ver) : InterpreterHandler(Output, _ver.kmodule->getModuleIdentifier()), ver(_ver) {
    if (IndentJson) indentation = "  ";
  }
  ~ICmpKleeHandler() override = default;

  void onStateInitialize(ExecutionState &state) override {
    ver.initialState = new ExecutionState(state);
    getInterpreter()->getGlobalVariableMap(ver.global_map);
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
      ver.fn_returns.emplace_back(make_pair(returning, new ExecutionState(state)));
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

void load_blacklists(StateComparator &cmp, string filename) {

  if (!filename.empty()) {
    ifstream infile(filename);
    if (infile.is_open()) {
      Json::Value root;
      infile >> root;

      Json::Value &functions = root["functions"];
      for (unsigned idx = 0, end = functions.size(); idx < end; ++idx) {
        string fn = functions[idx].asString();
        cmp.blacklistFunction(fn);
      }

      Json::Value &types = root["types"];
      for (unsigned idx = 0, end = types.size(); idx < end; ++idx) {
        string type = types[idx].asString();
        cmp.blacklistStructType(type);
      }
    }
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
      errs() << "not prepared: " << module->getModuleIdentifier() << '\n';
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

void getModuleNames(const string &dir, string &name1, string &name2, bool &with_oracle) {

  name1 = PreModule;
  name2 = PostModule;

  with_oracle = false;

  if (name1.empty() || name2.empty()) {
    if (fs::is_directory(dir)) {
      for (fs::directory_iterator itr{dir}, end{}; itr != end; ++itr) {
        fs::path pfile(itr->path());
        if (fs::is_regular_file(pfile) && (pfile.extension().string() == ".bc")) {

          string filename = pfile.filename().string();
          if (boost::starts_with(filename, "pre-")) {
            name1 = (fs::path(dir) / filename).string();
          } else if (boost::starts_with(filename, "rply-")) {
            name2 = (fs::path(dir) / filename).string();
            with_oracle = true;
          } else if (name2.empty() && boost::starts_with(filename, "post-")) {
            name2 = (fs::path(dir) / filename).string();
          }
        }
      }
    }
  }
}

void load_diff_info(const string &diff_file, KModule *kmod_pre, KModule *kmod_post) {

  string filename = diff_file;
  if (filename.empty()) {
    filename = (fs::path(Output)/"diff.json").string();
  }
  ifstream infile(filename);
  if (infile.is_open()) {
    Json::Value root;
    infile >> root;

    Json::Value &fns = root["functions"];
    Json::Value &fns_added = fns["added"];
    for (unsigned idx = 0, end = fns_added.size(); idx < end; ++idx) {
      kmod_post->addDiffFnAdded(fns_added[idx].asString());
    }
    Json::Value &fns_removed = fns["removed"];
    for (unsigned idx = 0, end = fns_removed.size(); idx < end; ++idx) {
      kmod_pre->addDiffFnRemoved(fns_removed[idx].asString());
    }
    Json::Value &fns_body = fns["body"];
    for (unsigned idx = 0, end = fns_body.size(); idx < end; ++idx) {
      string str = fns_body[idx].asString();
      kmod_pre->addDiffFnChangedBody(str);
      kmod_post->addDiffFnChangedBody(str);
    }
    Json::Value &fns_sig = fns["signature"];
    for (unsigned idx = 0, end = fns_sig.size(); idx < end; ++idx) {
      string str = fns_sig[idx].asString();
      kmod_pre->addDiffFnChangedSig(str);
      kmod_post->addDiffFnChangedSig(str);
    }

    Json::Value &gbs = root["globals"];
    Json::Value &gbs_added = gbs["added"];
    for (unsigned idx = 0, end = gbs_added.size(); idx < end; ++idx) {
      kmod_post->addDiffGlobalAdded(gbs_added[idx].asString());
    }
    Json::Value &gbs_removed = gbs["removed"];
    for (unsigned idx = 0, end = gbs_removed.size(); idx < end; ++idx) {
      kmod_pre->addDiffGlobalRemoved(gbs_removed[idx].asString());
    }

    Json::Value &gbs_type = gbs["changed"];
    for (unsigned idx = 0, end = gbs_type.size(); idx < end; ++idx) {
      string str = gbs_type[idx].asString();
      kmod_pre->addDiffGlobalChanged(str);
      kmod_post->addDiffGlobalChanged(str);
    }

    kmod_pre->pre_module = kmod_post->pre_module = root["pre-module"].asString();
    kmod_pre->post_module = kmod_post->post_module = root["post-module"].asString();
  } else {
    klee_error("failed opening diff file: %s", filename.c_str());
  }
}

int main(int argc, char **argv, char **envp) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();
  sys::SetInterruptFunction(interrupt_handle);

  // write out command line info, for reference
  if (ShowArgs) show_args(argc, argv);

  exit_code = 0;

  // if pre and post module are empty (default) then try to automatically find
  // pre and post modules in the output directory
  string mod_name1;
  string mod_name2;
  bool with_oracle = false;
  getModuleNames(Output, mod_name1, mod_name2, with_oracle);
  if (mod_name1.empty()) {
    errs() << "Failed to find pre-module\n";
    exit(1);
  }
  if (mod_name2.empty()) {
    errs() << "Failed to find post-module\n";
    exit(1);
  }

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
  load_diff_info(DiffInfo, kmod1, kmod2);

  LLVMContext *ctx1 = nullptr;
  LLVMContext *ctx2 = nullptr;
  ctx1 = kmod1->getContextPtr();
  ctx2 = kmod2->getContextPtr();

  deque<string> test_files;
  expand_test_files(Prefix, test_files);

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
      load_test_case(root, test);
    }
    if (!test.is_ready()) {
      klee_error("failed to load test case '%s'", test_file.c_str());
    }

    // Common setup
    Interpreter::InterpreterOptions IOpts;
    IOpts.mode = ExecModeID::rply;
    IOpts.user_mem_base = (void *) 0x90000000000;
    IOpts.user_mem_size = (0xa0000000000 - 0x90000000000);
    IOpts.trace = test.trace_type;
    IOpts.test_objs = &test.objects;
    UnconstraintFlagsT flags;
    IOpts.progression.emplace_back(Timeout, flags);

    StateVersion version1(kmod1);
    StateVersion version2(kmod2);

    auto *handler1 = new ICmpKleeHandler(version1);
    Interpreter *interpreter1 = Interpreter::createLocal(*ctx1, IOpts, handler1);
    handler1->setInterpreter(interpreter1);
    interpreter1->bindModule(kmod1);

    theInterpreter = interpreter1;
    interpreter1->runFunctionTestCase(test);
    theInterpreter = nullptr;

    if (version1.finalState != nullptr) {

      if (version1.finalState->status != StateStatus::Completed) {
        continue;
      }

      outs() << fs::path(test_file).filename().string() << ';' << oflush;

      // now, lets do it all again with the second module
      auto *handler2 = new ICmpKleeHandler(version2);
      Interpreter *interpreter2 = Interpreter::createLocal(*ctx2, IOpts, handler2);
      handler2->setInterpreter(interpreter2);
      interpreter2->bindModule(kmod2);

      theInterpreter = interpreter2;
      interpreter2->runFunctionTestCase(test);
      theInterpreter = nullptr;

      StateComparator cmp(test, version1, version2);
      load_blacklists(cmp, BlackLists);

      if (cmp.reachedChanged()) {
        const KInstruction *ki =  cmp.checkTermination();
        if (ki == nullptr) {
          if (cmp.isEquivalent()) {
            outs() << "equivalent;0;";
            if (with_oracle) {
              if (!cmp.beseechOracle()) {
                outs() << '-';
              } else {
                outs() << '+';
              }
            } else {
              outs() << '?';
            }
            outs() << oendl;
          } else {
            outs() << "divergent;" << cmp.checkpoints.size() << ';';
            if (with_oracle) {
              if (cmp.beseechOracle()) {
                outs() << '-';
              } else {
                outs() << '+';
              }
            } else {
              outs() << '?';
            }
            outs() << oendl;

            for (const auto &cp : cmp.checkpoints) {
              outs().indent(2) << to_string(cp) << oendl;
              for (const auto &diff : cp.diffs) {
                outs().indent(4) << to_string(diff) << oendl;
              }
            }
          }
        } else outs() << "diff (termination)" << " L" << ki->info->assemblyLine <<" (" << ki->info->file << ':' << ki->info->line << ')' << oendl;
      } else outs() << "discarded (did not reach)\n";
      delete interpreter2;
      delete handler2;
    } else {
      errs() << fs::path(test_file).filename().string() << ": " << "version1 timeout" << oendf;
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

  return exit_code;
}
