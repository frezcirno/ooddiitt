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
#include "klee/Config/CompileTimeInfo.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
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
#include <boost/filesystem.hpp>
#include <klee/Internal/Support/ModuleUtil.h>
#include "json/json.h"
#include "klee/TestCase.h"
#include "klee/util/CommonUtil.h"

using namespace llvm;
using namespace klee;
using namespace std;
namespace fs=boost::filesystem;

namespace {

  cl::opt<string> InputFile(cl::desc("<bytecode>"), cl::Positional, cl::Required);
  cl::list<string> InputArgv(cl::ConsumeAfter, cl::desc("<program arguments>..."));
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
  cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));
  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"));
  cl::opt<bool> Verbose("verbose", cl::init(false), cl::desc("Emit verbose output"));
  cl::opt<bool> TraceNone("trace-none", cl::init(false), cl::desc("disable tracing"));
  cl::opt<bool> TraceAssembly("trace-assm", cl::init(false), cl::desc("trace assembly lines"));
  cl::opt<bool> TraceStatements("trace-stmt", cl::init(false), cl::desc("trace source lines (does not capture filename)"));
  cl::opt<bool> TraceBBlocks("trace-bblk", cl::init(false), cl::desc("trace basic block markers"));
  cl::opt<string> UserMain("user-main", cl::desc("Consider the function with the given name as the main point"), cl::init("main"));
  cl::opt<string> TargetFn("target-fn", cl::desc("save snapshot at entry to function"), cl::Required);
  cl::opt<string> StdInText("stdin-text", cl::desc("text to inject into test as stdin"));
  cl::opt<string> StdInData("stdin-data", cl::desc("data block to inject into test as stdin"));
  cl::opt<string> Prefix("prefix", cl::desc("prefix for emitted test cases"), cl::init("test"));
  cl::opt<bool> ShowArgs("show-args", cl::desc("show invocation command line args"));
}

/***/

class RecordKleeHandler : public InterpreterHandler {
private:
  unsigned nextTestCaseID;
  unsigned casesGenerated;
  string indentation;
  const vector<string> &args;
  sys_clock::time_point started_at;
  bool is_main;

public:
  RecordKleeHandler(const vector<string> &args, const string &_md_name, const string &_prefix, bool as_main = false);
  ~RecordKleeHandler() override = default;

  unsigned getNumCasesGenerated() const { return casesGenerated; }
  void processTestCase(ExecutionState &state, TerminateReason reason) override;
};

RecordKleeHandler::RecordKleeHandler(const vector<string> &_args, const string &_md_name, const string &_prefix, bool as_main)
    : InterpreterHandler(Output, _md_name, _prefix),
      nextTestCaseID(0),
      casesGenerated(0),
      indentation(""),
      args(_args),
      is_main(as_main) {

  started_at = sys_clock::now();

  // if the directory was not newly created, then we need to find the next available case id
  if (!wasOutputCreated()) {

    // find the next available test id
    bool done = false;
    while (!done) {

      // find the next missing test case id.

      fs::path filename(getOutputFilename(getTestFilename("json", nextTestCaseID)));
      if (fs::exists(filename)) {
        ++nextTestCaseID;
      } else {
        done = true;
      }
    }
  }
  if (IndentJson) indentation = "  ";
}

/* Outputs all files (.ktest, .kquery, .cov etc.) describing a test case */
void RecordKleeHandler::processTestCase(ExecutionState &state, TerminateReason reason) {

  Interpreter *i = getInterpreter();
  assert(!state.isProcessed);

  if (i != nullptr && !NoOutput && (reason == TerminateReason::Snapshot)) {

    const Interpreter::InterpreterOptions &opts = i->getOptions();

    // select the next test id for this function
    unsigned testID = nextTestCaseID++;
    ofstream fout;
    string filename;
    if (openTestCaseFile(fout, testID, filename)) {

      outs() << "writing " << filename << '\n';

      // construct the json object representing the test case
      Json::Value root = Json::objectValue;
      root["module"] = getModuleName();
      root["file"] = getFileName();
      root["entryFn"] = opts.userSnapshot->getName().str();
      root["testID"] = testID;
      root["argC"] = args.size();
      root["lazyAllocationCount"] = state.lazyAllocationCount;
      root["maxLoopIteration"] = state.maxLoopIteration;
      root["maxLoopForks"] = state.maxLoopForks;
      root["maxLazyDepth"] = state.maxLazyDepth;
      root["timeStarted"] = to_string(started_at);
      root["timeStopped"] = currentISO8601TimeUTC();

      const UnconstraintFlagsT *flags = i->getUnconstraintFlags();
      if (flags != nullptr) {
        root["unconstraintFlags"] = flags->to_string();
        root["unconstraintDescription"] = klee::to_string(*flags);
      }
      root["kleeRevision"] = KLEE_BUILD_REVISION;
      root["termination"] = (unsigned) reason;
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

      stringstream ss;
      for (unsigned index = 0; index < args.size(); ++index) {
        if (index > 0) ss << ' ';
        ss << '\'' << args[index] << '\'';
      }
      root["argV"] = ss.str();
      root["stdin"] = toDataString(state.stdin_buffer);

      vector<ConcreteSolution> out;
      set<MemKind> memKinds;
      memKinds.insert(MemKind::external);
      if (!is_main) {
        memKinds.insert(MemKind::param);
        memKinds.insert(MemKind::global);
        memKinds.insert(MemKind::heap);
        memKinds.insert(MemKind::output);
        memKinds.insert(MemKind::lazy);
        memKinds.insert(MemKind::alloca_l);
      }

      if (!i->getConcreteSolution(state, out, memKinds)) {
        klee_warning("unable to get symbolic solution, losing test case");
      }

      Json::Value &objects = root["objects"] = Json::arrayValue;

      unsigned ptr_width = (Context::get().getPointerWidth() / 8);
      for (auto itrObj = out.begin(), endObj = out.end(); itrObj != endObj; ++itrObj) {

        auto &test = *itrObj;
        const MemoryObject *mo = test.first;
        vector<unsigned char> &data = test.second;

        Json::Value obj = Json::objectValue;
        obj["name"] = mo->name;
        obj["kind"] = (unsigned) mo->kind;
        obj["count"] = mo->count;
        obj["type"] = to_string(mo->type);

        // scale to 32 or 64 bits
        vector<unsigned char> addr;
        unsigned char *addrBytes = ((unsigned char *) &(test.first->address));
        for (unsigned index = 0; index < ptr_width; ++index, ++addrBytes) {
          addr.push_back(*addrBytes);
        }
        obj["addr"] = toDataString(addr);
        obj["data"] = toDataString(data);
        obj["align"] = mo->align;

        objects.append(obj);
      }

      Json::Value &arguments = root["arguments"] = Json::arrayValue;
      for (auto itr = state.arguments.begin(), end = state.arguments.end(); itr != end; ++itr) {
        klee::ref<klee::Expr> e = *itr;
        if (isa<klee::ConstantExpr>(e)) {
          klee::ref<klee::ConstantExpr> ce = cast<klee::ConstantExpr>(e);
          if (ce.isNull()) {
            arguments.append("");
          } else {
            uint64_t value = ce->getZExtValue();
            unsigned width = ce->getWidth() / 8;
            // have to adject for bools.  they are only 1-bit wide
            if (width == 0) width = 1;
            auto *byte = (unsigned char *) (&value);
            vector<unsigned char> v;
            for (unsigned idx = 0; idx < width; ++idx) {
              v.push_back(*byte++);
            }
            arguments.append(toDataString(v));
          }
        }
      }

      TraceType trace_type = i->getTraceType();
      if (trace_type != TraceType::invalid) {
        root["traceType"] = (unsigned) trace_type;
        Json::Value &trace = root["trace"] = Json::arrayValue;
        for (auto entry : state.trace) {
          trace.append(entry);
        }
      }

      // write the constructed json object to file
      Json::StreamWriterBuilder builder;
      builder["commentStyle"] = "None";
      builder["indentation"] = indentation;
      unique_ptr<Json::StreamWriter> writer(builder.newStreamWriter());

      writer->write(root, &fout);
      fout << endl;
      state.isProcessed = true;
      casesGenerated++;
    } else {
      klee_warning("unable to write output test case, losing it");
    }
  }
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

int main(int argc, char **argv, char **envp) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();
  sys::SetInterruptFunction(interrupt_handle);

  // write out command line info, for reference
  if (ShowArgs) show_args(argc, argv);

  exit_code = 0;

  // Load the bytecode...
  // load the bytecode emitted in the generation step...
  KModule *kmod = PrepareModule(InputFile);
  LLVMContext *ctx = nullptr;
  if (kmod != nullptr) {
    ctx = kmod->getContextPtr();
    if (Function *mainFn = kmod->getFunction(UserMain)) {
      if (Function *targetFn = kmod->getFunction(TargetFn)) {

        // setup arguments as from command line
        vector<string> args;
        args.reserve(InputArgv.size() + 1);
        args.push_back(InputFile);
        args.insert(args.end(), InputArgv.begin(), InputArgv.end());

        // now preload the stdin buffer
        vector<unsigned char> stdin_buffer;
        if (!StdInData.empty()) {
          fromDataString(stdin_buffer, StdInData);
        } else if (!StdInText.empty()) {
          stdin_buffer.reserve(StdInData.size());
          for (char ch : StdInText) {
            stdin_buffer.push_back(ch);
            stdin_buffer.push_back('\n');
          }
        }

        auto *handler = new RecordKleeHandler(args, kmod->getModuleIdentifier(), Prefix, mainFn == targetFn);

        Interpreter::InterpreterOptions IOpts;
        IOpts.mode = ExecModeID::irec;
        IOpts.user_mem_base = (void *) 0x80000000000;
        IOpts.user_mem_size = (0x90000000000 - 0x80000000000);
        IOpts.verbose = Verbose;
        IOpts.userSnapshot = targetFn;
        UnconstraintFlagsT flags;
        IOpts.progression.emplace_back(300, flags);

        if (TraceNone) {
          IOpts.trace = TraceType::none;
        } else if (TraceBBlocks) {
          IOpts.trace = TraceType::bblocks;
        } else if (TraceAssembly) {
          IOpts.trace = TraceType::assembly;
        } else if (TraceStatements) {
          IOpts.trace = TraceType::statements;
        }

        theInterpreter = Interpreter::createLocal(*ctx, IOpts, handler);
        handler->setInterpreter(theInterpreter);
        theInterpreter->bindModule(kmod);
        theInterpreter->runMainConcrete(mainFn, args, stdin_buffer, targetFn);

        if (handler->getNumCasesGenerated() == 0) {
          errs() << "target function \'" << TargetFn << "\' not reached\n";
          exit_code = 1;
        }

        delete theInterpreter;
        delete handler;
      } else {
        errs() << "Module function not found: " << TargetFn << '\n';
      }
    } else {
      errs() << "Module function not found: " << UserMain << '\n';
    }
    delete kmod;
    delete ctx;
  }
  return exit_code;
}
