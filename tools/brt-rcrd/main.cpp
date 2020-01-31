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
#include "klee/Config/CompileTimeInfo.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
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

using namespace llvm;
using namespace klee;
using namespace std;

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
}

/***/

class RecordKleeHandler : public InterpreterHandler {
private:
  unsigned nextTestCaseID;
  string indentation;
  const vector<string> &args;
  boost::filesystem::path outputDirectory;
  string md_name;
  string file_name;
  sys_clock::time_point started_at;

public:
  RecordKleeHandler(const vector<string> &args, const string &_md_name);
  ~RecordKleeHandler();

  void setInterpreter(Interpreter *i) override;

  void processTestCase(ExecutionState  &state) override;

  string toDataString(const vector<unsigned char> &data) const;

  string getOutputFilename(const string &filename) override;
  string getTestFilename(const string &prefix, const string &ext, unsigned id);
  string getModuleName() const override { return md_name; }

  ostream *openTestCaseFile(const string &prefix, unsigned testID);
  llvm::raw_fd_ostream *openTestFile(const string &prefix, const string &ext, unsigned id);
  llvm::raw_fd_ostream *openOutputFile(const string &filename, bool overwrite=false) override;
  llvm::raw_fd_ostream *openOutputAssembly() override { return openOutputFile(md_name + ".ll", false); }
  llvm::raw_fd_ostream *openOutputBitCode() override { return openOutputFile(md_name + ".bc", false); }

  static string getRunTimeLibraryPath(const char *argv0);

};

RecordKleeHandler::RecordKleeHandler(const vector<string> &_args, const string &_md_name)
    : nextTestCaseID(0),
      indentation(""),
      args(_args),
      outputDirectory(Output) {


  // create output directory (if required)
  bool created = false;
  started_at = sys_clock::now();

  boost::system::error_code ec;
  if (boost::filesystem::exists(outputDirectory)) {
  } else {
    boost::filesystem::create_directories(outputDirectory, ec);
    created = true;
  }

  // if the directory was not newly created, then we need to find the next available case id
  if (!created) {

    // find the next available test id
    bool done = false;
    while (!done) {

      // find the next missing test case id.
      string testname = getOutputFilename(getTestFilename("test", "json", nextTestCaseID));
      boost::filesystem::path testfile(testname);
      if (boost::filesystem::exists(testfile)) {
        ++nextTestCaseID;
      } else {
        done = true;
      }
    }
  }

  file_name = _md_name;
  md_name = boost::filesystem::path(_md_name).stem().string();
  if (IndentJson) indentation = "  ";
}

RecordKleeHandler::~RecordKleeHandler() {

}

void RecordKleeHandler::setInterpreter(Interpreter *i) {

  InterpreterHandler::setInterpreter(i);
}

string RecordKleeHandler::getOutputFilename(const string &filename) {

  boost::filesystem::path file = outputDirectory;
  file /= filename;
  return file.string();
}

llvm::raw_fd_ostream *RecordKleeHandler::openOutputFile(const string &filename, bool overwrite) {
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

string RecordKleeHandler::getTestFilename(const string &prefix, const string &ext, unsigned id) {
  stringstream filename;
  filename << prefix << setfill('0') << setw(10) << id << '.' << ext;
  return filename.str();
}

llvm::raw_fd_ostream *RecordKleeHandler::openTestFile(const string &prefix, const string &ext, unsigned id) {
  return openOutputFile(getTestFilename(prefix, ext, id));
}

ostream *RecordKleeHandler::openTestCaseFile(const string &prefix, unsigned testID) {

  ofstream *result = nullptr;
  string filename = getTestFilename(prefix, "json", testID);
  outs() << "writing " << filename << '\n';
  string pathname = getOutputFilename(filename);
  result = new ofstream(pathname);
  if (result != nullptr) {
    if (!result->is_open()) {
      delete result;
      result = nullptr;
    }
  }
  return result;
}

string RecordKleeHandler::toDataString(const vector<unsigned char> &data) const {

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

/* Outputs all files (.ktest, .kquery, .cov etc.) describing a test case */
void RecordKleeHandler::processTestCase(ExecutionState &state) {

  Interpreter *i = getInterpreter();
  const Interpreter::InterpreterOptions &opts = i->getOptions();

  assert(!state.isProcessed);

  if (i != nullptr && !NoOutput && (state.status == StateStatus::Snapshot)) {

    // select the next test id for this function
    unsigned testID = nextTestCaseID++;
    string prefix = "test";
    ostream *kout = openTestCaseFile(prefix, testID);
    if (kout != nullptr) {

      // construct the json object representing the test case
      Json::Value root = Json::objectValue;
      root["module"] = md_name;
      root["file"] = file_name;
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
      root["status"] = (unsigned) state.status;
      if (state.instFaulting != nullptr) {
        root["instFaulting"] = state.instFaulting->info->assemblyLine;
      }
      root["message"] = state.terminationMessage;

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
      if (!i->getConcreteSolution(state, out)) {
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

      writer->write(root, kout);
      *kout << endl;

      kout->flush();
      delete kout;
      state.isProcessed = true;
    } else {
      klee_warning("unable to write output test case, losing it");
    }
  }
}

string RecordKleeHandler::getRunTimeLibraryPath(const char *argv0) {
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
          TestObject::fromDataString(stdin_buffer, StdInData);
        } else if (!StdInText.empty()) {
          stdin_buffer.reserve(StdInData.size());
          for (char ch : StdInText) {
            stdin_buffer.push_back(ch);
          }
        }

        auto *handler = new RecordKleeHandler(args, kmod->getModuleIdentifier());

        Interpreter::InterpreterOptions IOpts;
        IOpts.mode = ExecModeID::irec;
        IOpts.user_mem_base = (void *) 0x80000000000;
        IOpts.user_mem_size = (0x90000000000 - 0x80000000000);
        IOpts.verbose = Verbose;
        IOpts.userSnapshot = targetFn;

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
