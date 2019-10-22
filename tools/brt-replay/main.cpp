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
#include "klee/Expr.h"
#include "klee/Interpreter.h"
#include "klee/Statistics.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Config/CompileTimeInfo.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/System/Memory.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Support/Timer.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/Errno.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"

#include <openssl/sha.h>
#include <boost/algorithm/hex.hpp>
#include <fstream>

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/system_error.h"
#endif

#include <dirent.h>
#include <signal.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>

#include <cerrno>
#include <string>
#include <fstream>
#include <iomanip>
#include <iterator>
#include <sstream>
#include <fcntl.h>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include <chrono>
#include "json/json.h"
#include "klee/TestCase.h"

using namespace llvm;
using namespace klee;
using namespace std;
typedef chrono::system_clock sys_clock;

namespace {

  cl::opt<string> InputFile1(cl::desc("<bytecode1>"), cl::Positional, cl::Required);
  cl::opt<string> InputFile2(cl::desc("<bytecode2>"), cl::Positional, cl::Required);
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<string> ReplayTest("replay-test", cl::desc("test case to replay"));
  cl::opt<string> RunInDir("run-in", cl::desc("Change to the given directory prior to executing"));
  cl::opt<string> Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));
  cl::list<string> InputArgv(cl::ConsumeAfter, cl::desc("<program arguments>..."));
  cl::opt<bool> NoOutput("no-output", cl::desc("Don't generate test files"));
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
  cl::opt<bool> ExitOnError("exit-on-error", cl::desc("Exit if errors occur"));

#if 0 == 1
  enum LibcType {
    NoLibc, KleeLibc, UcLibc
  };

  cl::opt<LibcType>
  Libc("libc",
       cl::desc("Choose libc version (none by default)."),
       cl::values(clEnumValN(NoLibc, "none", "Don't link in a libc"),
                  clEnumValN(KleeLibc, "klee", "Link in klee libc"),
		          clEnumValN(UcLibc, "uclibc", "Link in uclibc (adapted for klee)"),
		          clEnumValEnd),
       cl::init(UcLibc));

  cl::opt<bool>
  WithPOSIXRuntime("posix-runtime",
		cl::desc("Link with POSIX runtime.  Options that can be passed as arguments to the programs are: --sym-arg <max-len>  --sym-args <min-argvs> <max-argvs> <max-len> + file model options"),
		cl::init(false));

  cl::opt<bool> OptimizeModule("optimize", cl::desc("Optimize before execution"), cl::init(false));
  cl::opt<bool> CheckDivZero("check-div-zero", cl::desc("Inject checks for division-by-zero"), cl::init(false));
  cl::opt<bool> CheckOvershift("check-overshift", cl::desc("Inject checks for overshift"), cl::init(false));
  cl::list<string> LinkLibraries("link-llvm-lib", cl::desc("Link the given libraries before execution"), cl::value_desc("library file"));
#endif

  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-klee-tmp"));
  cl::opt<unsigned> Watchdog("watchdog", cl::desc("Use a watchdog process to monitor se. (default = 0 secs"), cl::init(0));
}

/***/

string to_string(const sys_clock::time_point &tp) {

  auto itt = sys_clock::to_time_t(tp);
  ostringstream ss;
  ss << put_time(gmtime(&itt), "%FT%TZ");
  return ss.str();
}

string currentISO8601TimeUTC() {
  return to_string(sys_clock::now());
}

class ReplayKleeHandler : public InterpreterHandler {
private:
  unsigned casesGenerated;
  string indentation;
  unsigned m_pathsExplored; // number of paths explored so far
  pid_t pid_watchdog;

  boost::filesystem::path outputDirectory;
  map<string,unsigned> terminationCounters;
  string md_name;
  set<ExecutionState*> &results;

public:
  ReplayKleeHandler(set<ExecutionState*> &_results, const string &_md_name);
  ~ReplayKleeHandler();

  llvm::raw_ostream &getInfoStream() const override { return outs(); }
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
  string getTypeName(const Type *Ty) const override;

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

ReplayKleeHandler::ReplayKleeHandler(set<ExecutionState*> &_results, const string &_md_name)
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
  outs() << "output directory: " << outputDirectory.string() << '\n';
  if (IndentJson) indentation = "  ";
}

ReplayKleeHandler::~ReplayKleeHandler() {
}

string ReplayKleeHandler::getTypeName(const Type *Ty) const {

  if (Ty != nullptr) {

    switch (Ty->getTypeID()) {
      case Type::VoidTyID: return "void";
      case Type::HalfTyID: return "half";
      case Type::FloatTyID: return "float";
      case Type::DoubleTyID: return "double";
      case Type::X86_FP80TyID: return "x86_fp80";
      case Type::FP128TyID: return "fp128";
      case Type::PPC_FP128TyID: return "ppc_fp128";
      case Type::LabelTyID: return "label";
      case Type::MetadataTyID: return "metadata";
      case Type::X86_MMXTyID: return "x86_mmx";
      case Type::IntegerTyID: {
        stringstream ss;
        ss << 'i' << cast<IntegerType>(Ty)->getBitWidth();
        return ss.str();
      }
      case Type::FunctionTyID: return "function";
      case Type::StructTyID: {
        const StructType *STy = cast<StructType>(Ty);
        return STy->getName().str();
      }
      case Type::PointerTyID: {

        stringstream ss;
        const PointerType *PTy = cast<PointerType>(Ty);
        ss << getTypeName(PTy->getElementType());
        ss << '*';
        return ss.str();
      }
      case Type::ArrayTyID: {

        stringstream ss;
        const ArrayType *ATy = cast<ArrayType>(Ty);
        ss << '[' << ATy->getNumElements() << " x ";
        ss << getTypeName(ATy->getElementType());
        ss << ']';
        return ss.str();
      }
      case Type::VectorTyID: {
        stringstream ss;
        const VectorType *VTy = cast<VectorType>(Ty);
        ss << '<' << VTy->getNumElements() << " x ";
        ss << getTypeName(VTy->getElementType());
        ss << '>';
        return ss.str();
      }
      default: {

      }
    }
  }

  return "";
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

  results.insert(new ExecutionState(state));

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
static string strip(const string &in) {
  unsigned len = in.size();
  unsigned lead = 0, trail = len;
  while (lead<len && isspace(in[lead]))
    ++lead;
  while (trail>lead && isspace(in[trail-1]))
    --trail;
  return in.substr(lead, trail-lead);
}

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

// This is a terrible hack until we get some real modeling of the
// system. All we do is check the undefined symbols and warn about
// any "unrecognized" externals and about any obviously unsafe ones.

// Symbols we explicitly support
static const char *modelledExternals[] = {
  "_ZTVN10__cxxabiv117__class_type_infoE",
  "_ZTVN10__cxxabiv120__si_class_type_infoE",
  "_ZTVN10__cxxabiv121__vmi_class_type_infoE",

  // special functions
  "_assert",
  "__assert_fail",
  "__assert_rtn",
  "calloc",
  "_exit",
  "exit",
  "free",
  "abort",
  "klee_abort",
  "klee_assume",
  "klee_check_memory_access",
  "klee_define_fixed_object",
  "klee_get_errno",
  "klee_get_valuef",
  "klee_get_valued",
  "klee_get_valuel",
  "klee_get_valuell",
  "klee_get_value_i32",
  "klee_get_value_i64",
  "klee_get_obj_size",
  "klee_is_symbolic",
  "klee_make_symbolic",
  "klee_mark_global",
  "klee_merge",
  "klee_prefer_cex",
  "klee_posix_prefer_cex",
  "klee_print_expr",
  "klee_print_range",
  "klee_report_error",
  "klee_set_forking",
  "klee_silent_exit",
  "klee_warning",
  "klee_warning_once",
  "klee_alias_function",
  "klee_stack_trace",
  "llvm.dbg.declare",
  "llvm.dbg.value",
  "llvm.va_start",
  "llvm.va_end",
  "malloc",
  "realloc",
  "_ZdaPv",
  "_ZdlPv",
  "_Znaj",
  "_Znwj",
  "_Znam",
  "_Znwm",
  "__ubsan_handle_add_overflow",
  "__ubsan_handle_sub_overflow",
  "__ubsan_handle_mul_overflow",
  "__ubsan_handle_divrem_overflow",

  // ignore marker instrumentation
  "__mark__",
  "__MARK__",
  "__calltag__",
  "__init_markers__",
  "__term_markers__",

  // special pgklee functions
  "pgklee_hard_assume",
  "pgklee_soft_assume",
  "pgklee_implies",
  "pgklee_expr_holds",
  "pgklee_expr_mayhold",
  "pgklee_valid_pointer",
  "pgklee_object_size"
};
// Symbols we aren't going to warn about
static const char *dontCareExternals[] = {

  // static information, pretty ok to return
  "getegid",
  "geteuid",
  "getgid",
  "getuid",
  "getpid",
  "gethostname",
  "getpgrp",
  "getppid",
  "getpagesize",
  "getpriority",
  "getgroups",
  "getdtablesize",
  "getrlimit",
  "getrlimit64",
  "getcwd",
  "getwd",
  "gettimeofday",
  "uname",

  // fp stuff we just don't worry about yet
  "frexp",
  "ldexp",
  "__isnan",
  "__signbit",
};
// Extra symbols we aren't going to warn about with klee-libc
static const char *dontCareKlee[] = {
  "__ctype_b_loc",
  "__ctype_get_mb_cur_max",

  // io system calls
  "open",
  "write",
  "read",
  "close",
};
// Extra symbols we aren't going to warn about with uclibc
static const char *dontCareUclibc[] = {
  "__ctype_b_loc",
  "__dso_handle",

  // Don't warn about these since we explicitly commented them out of
  // uclibc.
  "printf",
  "vprintf"
};
// Symbols we consider unsafe
//static const char *unsafeExternals[] = {
//  "fork", // oh lord
//  "exec", // heaven help us
//  "error", // calls _exit
//  "raise", // yeah
//  "kill", // mmmhmmm
//};

#define NELEMS(array) (sizeof(array)/sizeof(array[0]))

void externalsAndGlobalsCheck(const Module *m, bool emit_warnings) {
  set<string> modelled(modelledExternals, modelledExternals+NELEMS(modelledExternals));
  set<string> dontCare(dontCareExternals, dontCareExternals+NELEMS(dontCareExternals));

#if 0 == 1
  switch (Libc) {
  case KleeLibc:
    dontCare.insert(dontCareKlee, dontCareKlee+NELEMS(dontCareKlee));
    break;
  case UcLibc:
    dontCare.insert(dontCareUclibc,
                    dontCareUclibc+NELEMS(dontCareUclibc));
    break;
  case NoLibc: /* silence compiler warning */
    break;
  }

  if (WithPOSIXRuntime)
    dontCare.insert("syscall");
#endif

  set<string> extFunctions;
  set<string> extGlobals;

  // get a list of functions declared, but not defined
  for (Module::const_iterator fnIt = m->begin(), fn_ie = m->end(); fnIt != fn_ie; ++fnIt) {
    if (fnIt->isDeclaration() && !fnIt->use_empty()) {
      string name = fnIt->getName();
      if (modelled.count(name) == 0 && dontCare.count(name) == 0) {
        extFunctions.insert(fnIt->getName());
      }
    }

    if (emit_warnings) {
      // check for inline assembly
      for (Function::const_iterator bbIt = fnIt->begin(), bb_ie = fnIt->end(); bbIt != bb_ie; ++bbIt) {
        for (BasicBlock::const_iterator it = bbIt->begin(), ie = bbIt->end(); it != ie; ++it) {
          if (const CallInst *ci = dyn_cast<CallInst>(it)) {
            if (isa<InlineAsm>(ci->getCalledValue())) {
                klee_warning_once(&*fnIt, "function \"%s\" has inline asm", fnIt->getName().data());
            }
          }
        }
      }
    }
  }

  // get a list of globals declared, but not defined
  for (Module::const_global_iterator it = m->global_begin(), ie = m->global_end(); it != ie; ++it) {
    if (it->isDeclaration() && !it->use_empty()) {
      extGlobals.insert(it->getName());
    }
  }
  // and remove aliases (they define the symbol after global
  // initialization)
  for (Module::const_alias_iterator it = m->alias_begin(), ie = m->alias_end(); it != ie; ++it) {
    auto it2 = extFunctions.find(it->getName());
    if (it2!=extFunctions.end()) {
      extFunctions.erase(it2);
  }
    auto it3 = extGlobals.find(it->getName());
    if (it3!=extGlobals.end()) {
      extGlobals.erase(it3);
    }
  }

  if (emit_warnings) {
    for (auto fn: extFunctions) {
      klee_warning("reference to external function: %s", fn.c_str());
    }
    for (auto global: extGlobals) {
      klee_warning("reference to undefined global: %s", global.c_str());
    }
  }
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

#if 0 == 1
#ifndef SUPPORT_KLEE_UCLIBC
static llvm::Module *linkWithUclibc(llvm::Module *mainModule, StringRef libDir) {
  klee_error("invalid libc, no uclibc support!\n");
}
#else
static void replaceOrRenameFunction(llvm::Module *module,
		const char *old_name, const char *new_name)
{
  Function *f, *f2;
  f = module->getFunction(new_name);
  f2 = module->getFunction(old_name);
  if (f2) {
    if (f) {
      f2->replaceAllUsesWith(f);
      f2->eraseFromParent();
    } else {
      f2->setName(new_name);
      assert(f2->getName() == new_name);
    }
  }
}

static llvm::Module *linkWithUclibc(llvm::Module *mainModule, StringRef libDir) {

  LLVMContext &ctx = mainModule->getContext();
  // Ensure that klee-uclibc exists
  SmallString<128> uclibcBCA(libDir);

  string uclibcLib = "klee-uclibc";
  string extension = ".bca";
  llvm::DataLayout targetData(mainModule);
  Expr::Width width = targetData.getPointerSizeInBits();
  if (width == Expr::Int32) {
    uclibcLib += "-32";
  } else if (width == Expr::Int64) {
    uclibcLib += "-64";
  }
  uclibcLib += extension;
  llvm::sys::path::append(uclibcBCA, uclibcLib);

  bool uclibcExists=false;
  llvm::sys::fs::exists(uclibcBCA.c_str(), uclibcExists);
  if (!uclibcExists)
    klee_error("Cannot find klee-uclibc : %s", uclibcBCA.c_str());

  // RLR TODO: evaluate how much of this we really need
  Function *f;
  // force import of __uClibc_main
  mainModule->getOrInsertFunction("__uClibc_main", FunctionType::get(Type::getVoidTy(ctx), vector<LLVM_TYPE_Q Type*>(), true));

  // force various imports
  if (WithPOSIXRuntime) {
    LLVM_TYPE_Q llvm::Type *i8Ty = Type::getInt8Ty(ctx);
    mainModule->getOrInsertFunction("realpath",
                                    PointerType::getUnqual(i8Ty),
                                    PointerType::getUnqual(i8Ty),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("getutent",
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("__fgetc_unlocked",
                                    Type::getInt32Ty(ctx),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("__fputc_unlocked",
                                    Type::getInt32Ty(ctx),
                                    Type::getInt32Ty(ctx),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
  }

  f = mainModule->getFunction("__ctype_get_mb_cur_max");
  if (f) f->setName("_stdlib_mb_cur_max");

  // Strip of asm prefixes for 64 bit versions because they are not
  // present in uclibc and we want to make sure stuff will get
  // linked. In the off chance that both prefixed and unprefixed
  // versions are present in the module, make sure we don't create a
  // naming conflict.
  for (Module::iterator fi = mainModule->begin(), fe = mainModule->end(); fi != fe; ++fi) {
    Function *f = static_cast<Function *>(fi);
    const string &name = f->getName();
    if (name[0]=='\01') {
      unsigned size = name.size();
      if (name[size-2]=='6' && name[size-1]=='4') {
        string unprefixed = name.substr(1);

        // See if the unprefixed version exists.
        if (Function *f2 = mainModule->getFunction(unprefixed)) {
          f->replaceAllUsesWith(f2);
          f->eraseFromParent();
        } else {
          f->setName(unprefixed);
        }
      }
    }
  }

  mainModule = klee::linkWithLibrary(mainModule, uclibcBCA.c_str());
  assert(mainModule && "unable to link with uclibc");

  replaceOrRenameFunction(mainModule, "__libc_open", "open");
  replaceOrRenameFunction(mainModule, "__libc_fcntl", "fcntl");

  // Take care of fortified functions
  replaceOrRenameFunction(mainModule, "__fprintf_chk", "fprintf");

  // XXX we need to rearchitect so this can also be used with
  // programs externally linked with uclibc.

  // RLR TODO: evaluate the continuing need for this
  // We now need to swap things so that __uClibc_main is the entry
  // point, in such a way that the arguments are passed to
  // __uClibc_main correctly. We do this by renaming the user main
  // and generating a stub function to call __uClibc_main. There is
  // also an implicit cooperation in that runFunctionAsMain sets up
  // the environment arguments to what uclibc expects (following
  // argv), since it does not explicitly take an envp argument.
//  Function *userMainFn = mainModule->getFunction(UserMain);
//  assert(userMainFn && "unable to get user main");
  Function *uclibcMainFn = mainModule->getFunction("__uClibc_main");
  assert(uclibcMainFn && "unable to get uclibc main");

  const FunctionType *ft = uclibcMainFn->getFunctionType();
  assert(ft->getNumParams() == 7);

  // and trivialize functions we will never use
  // RLR TODO: may need to trivialize or capture other functions
  set<string> trivialize_fns {
    "isatty",
    "tcgetattr",
    "__uClibc_main",
    "__check_one_fd",
    "__stdio_WRITE",
    "__stdio_wcommit",
    "_stdio_term"
  };

  for (auto name : trivialize_fns) {
    Function *fn;
    if ((fn = mainModule->getFunction(name)) != nullptr) {

      Type *rt = fn->getReturnType();
      fn->dropAllReferences();
      BasicBlock *bb = BasicBlock::Create(ctx, "entry", fn);

      if (rt->isVoidTy()) {
        ReturnInst::Create(ctx, bb);
      } else if (rt->isIntegerTy()) {
        ReturnInst::Create(ctx, ConstantInt::get(rt, 0), bb);
      }
    }
  }

  outs() << "NOTE: Using klee-uclibc: " << uclibcBCA << '\n';
  return mainModule;
}
#endif

#endif

void load_test_case(Json::Value &root, TestCase &test) {

  // complete test case from json structure
  test.arg_c = root["argC"].asInt();
  test.arg_v = root["argV"].asString();
  test.entry_fn = root["entryFn"].asString();
  test.klee_version = root["kleeRevision"].asString();
  test.lazy_alloc_count = root["lazyAllocationCount"].isUInt();
  test.max_lazy_depth = root["maxLazyDepth"].isUInt();
  test.max_loop_forks = root["maxLoopForks"].isUInt();
  test.max_loop_iter = root["maxLoopIteration"].isUInt();
  test.message = root["message"].asString();
  test.path_condition_vars = root["pathConditionVars"].asString();
  test.status = root["status"].asString();;
  test.test_id = root["testID"].asUInt();

  Json::Value &objs = root["objects"];
  if (objs.isArray()) {
    for (unsigned idx = 0, end = objs.size(); idx < end; ++idx) {
      Json::Value &obj = objs[idx];
      string addr = obj["addr"].asString();
      unsigned count = obj["count"].asUInt();
      string data = obj["data"].asString();
      string kind = obj["kind"].asString();
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

  // Load the bytecode...
  // load the bytecode emitted in the generation step...

  string ErrorMsg;
  LLVMContext ctx;
  Module *mainModule1 = nullptr;
  OwningPtr<MemoryBuffer> BufferPtr1;
  llvm::error_code ec = MemoryBuffer::getFileOrSTDIN(InputFile1.c_str(), BufferPtr1);
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
  if (!mainModule1) klee_error("error loading program '%s': %s", InputFile1.c_str(), ErrorMsg.c_str());

#if 0 == 1
  if (WithPOSIXRuntime) {
    int r = initEnv(mainModule);
    klee_error("Failed initializing posix runtime, error=%d", r);
  }

  string LibraryDir = ReplayKleeHandler::getRunTimeLibraryPath(argv[0]);

  switch (Libc) {
  case NoLibc: /* silence compiler warning */
    break;

  // RLR TODO: uclibc is 64-bit only
  case KleeLibc: {
    // FIXME: Find a reasonable solution for this.
    SmallString<128> Path(LibraryDir);
    llvm::sys::path::append(Path, "klee-libc.bc");
    mainModule = klee::linkWithLibrary(mainModule, Path.c_str());
    assert(mainModule && "unable to link with klee-libc");
    break;
  }

  case UcLibc:
    mainModule = linkWithUclibc(mainModule, LibraryDir);
    break;
  }

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

  vector<string>::iterator libs_it;
  vector<string>::iterator libs_ie;
  for (libs_it = LinkLibraries.begin(), libs_ie = LinkLibraries.end();
          libs_it != libs_ie; ++libs_it) {
    const char * libFilename = libs_it->c_str();
    outs() << "Linking in library: " << libFilename << '\n';
    mainModule = klee::linkWithLibrary(mainModule, libFilename);
  }

  // FIXME: Change me to std types.
  int pArgc;
  char **pArgv;
  char **pEnvp;
  if (Environ != "") {
    vector<string> items;
    ifstream f(Environ.c_str());
    if (!f.good())
      klee_error("unable to open --environ file: %s", Environ.c_str());
    while (!f.eof()) {
      string line;
      getline(f, line);
      line = strip(line);
      if (!line.empty())
        items.push_back(line);
    }
    f.close();
    pEnvp = new char *[items.size()+1];
    unsigned i=0;
    for (; i != items.size(); ++i)
      pEnvp[i] = strdup(items[i].c_str());
    pEnvp[i] = 0;
  } else {
    pEnvp = envp;
  }

  pArgc = InputArgv.size() + 1;
  pArgv = new char *[pArgc];
  for (unsigned i=0; i<InputArgv.size()+1; i++) {
    string &arg = (i==0 ? InputFile : InputArgv[i-1]);
    unsigned size = arg.size() + 1;
    char *pArg = new char[size];

    copy(arg.begin(), arg.end(), pArg);
    pArg[size - 1] = 0;

    pArgv[i] = pArg;
  }

#endif

  set<ExecutionState*> completes1;
  ReplayKleeHandler *handler1 = new ReplayKleeHandler(completes1, mainModule1->getModuleIdentifier());
  handler1->setWatchDog(pid_watchdog);

  Interpreter::InterpreterOptions IOpts;
  IOpts.mode = Interpreter::ExecModeID::rply;

  theInterpreter = Interpreter::createLocal(ctx, IOpts, handler1);
  handler1->setInterpreter(theInterpreter);

  Interpreter::ModuleOptions MOpts;

  MOpts.LibraryDir = "";
  MOpts.Optimize = false;
  MOpts.CheckDivZero = false;
  MOpts.CheckOvershift = false;

  const Module *finalModule1 = theInterpreter->setModule(mainModule1, MOpts);

  externalsAndGlobalsCheck(finalModule1, true);

  auto start_time = sys_clock::now();
  handler1->getInfoStream() << "Started: " << to_string(start_time) << '\n';
  handler1->getInfoStream().flush();

  if (RunInDir != "") {
    int res = chdir(RunInDir.c_str());
    if (res < 0) {
      klee_error("Unable to change directory to: %s - %s", RunInDir.c_str(),
                 sys::StrError(errno).c_str());
    }
  }

  TestCase test;
  if (!ReplayTest.empty()) {

    ifstream info;
    info.open(ReplayTest);
    if (info.is_open()) {

      Json::Value root;
      info >> root;
      load_test_case(root, test);
      theInterpreter->runFunctionTestCase(test);
    }
  }

  auto finish_time = sys_clock::now();
  handler1->getInfoStream() << "Finished: " << to_string(finish_time) << '\n';
  auto elapsed = chrono::duration_cast<chrono::seconds>(finish_time - start_time);
  handler1->getInfoStream() << "Elapsed: " << elapsed.count() << '\n';

  Interpreter *interpreter1 = theInterpreter;
  theInterpreter = nullptr;

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  // FIXME: This really doesn't look right
  // This is preventing the module from being
  // deleted automatically
  BufferPtr1.take();
#endif


  // now, lets do it all again with the second module

  Module *mainModule2 = nullptr;
  OwningPtr<MemoryBuffer> BufferPtr2;
  ec = MemoryBuffer::getFileOrSTDIN(InputFile1.c_str(), BufferPtr2);
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
  if (!mainModule2) klee_error("error loading program '%s': %s", InputFile2.c_str(), ErrorMsg.c_str());

  set<ExecutionState*> completes2;
  ReplayKleeHandler *handler2 = new ReplayKleeHandler(completes2, mainModule1->getModuleIdentifier());
  handler2->setWatchDog(pid_watchdog);

  theInterpreter = Interpreter::createLocal(ctx, IOpts, handler2);
  handler2->setInterpreter(theInterpreter);
  const Module *finalModule2 = theInterpreter->setModule(mainModule2, MOpts);

  externalsAndGlobalsCheck(finalModule2, true);

  start_time = sys_clock::now();
  handler2->getInfoStream() << "Started: " << to_string(start_time) << '\n';
  handler2->getInfoStream().flush();

  theInterpreter->runFunctionTestCase(test);

  finish_time = sys_clock::now();
  handler2->getInfoStream() << "Finished: " << to_string(finish_time) << '\n';
  elapsed = chrono::duration_cast<chrono::seconds>(finish_time - start_time);
  handler2->getInfoStream() << "Elapsed: " << elapsed.count() << '\n';

  Interpreter *interpreter2 = theInterpreter;
  theInterpreter = nullptr;

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  // FIXME: This really doesn't look right
  // This is preventing the module from being
  // deleted automatically
  BufferPtr2.take();
#endif

  return exit_code;
}
