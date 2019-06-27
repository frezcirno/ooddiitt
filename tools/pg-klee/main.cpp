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
#include "json/json.h"
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
#include <klee/Internal/Module/KInstruction.h>

using namespace llvm;
using namespace klee;

namespace {

  cl::opt<std::string>
  InputFile(cl::desc("<input bytecode>"), cl::Positional, cl::init("-"));

  cl::opt<std::string>
  ProgramInfo("prog-info",
              cl::desc("json formated info from static analysis"),
              cl::init("prog-info.json"));

  cl::opt<bool>
  Verbose("verbose",
          cl::desc("verbose output text"),
          cl::init(false));

  cl::opt<std::string>
  SkipStartingBlocks("skip-starting-blocks",
                     cl::init(""),
                     cl::desc("When fragmenting, do not start from these block ids"));

cl::opt<bool>
  IndentJson("indent-json",
             cl::desc("indent emitted json for readability"),
             cl::init(false));

  cl::opt<std::string>
  EntryPoint("entry-point",
             cl::desc("Start local symbolic execution at entrypoint"),
             cl::init(""));

  cl::opt<int>
  StartCaseID("start-case-id",
              cl::init(-1),
              cl::desc("starting test case id"));

  cl::opt<std::string>
  UserMain("user-main",
           cl::desc("Consider the function with the given name as the main point"),
           cl::init("main"));

  cl::opt<std::string>
  Progression("progression",
              cl::desc("progressive phases of unconstraint (i:600,g:600,l:60,s:60)"),
              cl::init(""));

  cl::opt<Interpreter::ExecModeID>
  ExecMode("mode",
           cl::Required,
           cl::desc("pg-klee execution mode"),
           cl::values(
               clEnumValN(Interpreter::ExecModeID::zop, "zop", "configure for zop input generation"),
               clEnumValN(Interpreter::ExecModeID::fault, "fault", "configure for fault finding"),
               clEnumValEnd),
           cl::init(Interpreter::ExecModeID::none));

  cl::opt<bool>
  NoAddressSpace("no-address-space",
                 cl::desc("do not emit address space map with test cases"),
                 cl::init(false));

  cl::opt<std::string>
  RunInDir("run-in", cl::desc("Change to the given directory prior to executing"));

  cl::opt<std::string>
  Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));

  cl::list<std::string>
  InputArgv(cl::ConsumeAfter,
            cl::desc("<program arguments>..."));

  cl::opt<bool>
  NoOutput("no-output",
           cl::desc("Don't generate test files"));

  cl::opt<bool>
  WarnAllExternals("warn-all-externals",
                   cl::desc("Give initial warning for all externals."));

  cl::opt<bool>
  WriteCVCs("write-cvcs",
            cl::desc("Write .cvc files for each test case"));

  cl::opt<bool>
  WriteKQueries("write-kqueries",
            cl::desc("Write .kquery files for each test case"));

  cl::opt<bool>
  WriteSMT2s("write-smt2s",
            cl::desc("Write .smt2 (SMT-LIBv2) files for each test case"));

  cl::opt<bool>
  WriteCov("write-cov",
           cl::desc("Write coverage information for each test case"));

  cl::opt<bool>
  WriteTestInfo("write-test-info",
                cl::desc("Write additional test case information"));

  cl::opt<bool>
  WritePaths("write-paths",
                cl::desc("Write .path files for each test case"));

  cl::opt<bool>
  WriteSymPaths("write-sym-paths",
                cl::desc("Write .sym.path files for each test case"));

  cl::opt<bool>
  ExitOnError("exit-on-error",
              cl::desc("Exit if errors occur"));


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
       cl::init(NoLibc));


  cl::opt<bool>
  WithPOSIXRuntime("posix-runtime",
		cl::desc("Link with POSIX runtime.  Options that can be passed as arguments to the programs are: --sym-arg <max-len>  --sym-args <min-argvs> <max-argvs> <max-len> + file model options"),
		cl::init(false));

  cl::opt<bool>
  OptimizeModule("optimize",
                 cl::desc("Optimize before execution"),
		 cl::init(false));

  cl::opt<bool>
  CheckDivZero("check-div-zero",
               cl::desc("Inject checks for division-by-zero"),
               cl::init(true));

  cl::opt<bool>
  CheckOvershift("check-overshift",
               cl::desc("Inject checks for overshift"),
               cl::init(true));

  cl::opt<std::string>
  OutputCreate("output-create",
               cl::desc("recreate output directory (if it exists)"),
               cl::init(""));

  cl::opt<std::string>
  OutputAppend("output-append",
               cl::desc("add to existing output directory (fail if does not exist)"),
               cl::init(""));

  cl::opt<std::string>
  OutputPrefix("output-prefix",
               cl::desc("prefix for message files"),
               cl::init(""));

  cl::list<std::string>
  LinkLibraries("link-llvm-lib",
		cl::desc("Link the given libraries before execution"),
		cl::value_desc("library file"));

  cl::opt<unsigned>
  MakeConcreteSymbolic("make-concrete-symbolic",
                       cl::desc("Probabilistic rate at which to make concrete reads symbolic, "
				"i.e. approximately 1 in n concrete reads will be made symbolic (0=off, 1=all).  "
				"Used for testing."),
                       cl::init(0));

  cl::opt<bool>
  Watchdog("watchdog",
           cl::desc("Use a watchdog process to monitor se."),
           cl::init(0));


  cl::opt<bool>
  NoSolution("no-solution",
             cl::desc("Do not save a solution with test case."),
             cl::init(false));

}

/***/

class PGKleeHandler : public InterpreterHandler {
private:
  TreeStreamWriter *m_pathWriter, *m_symPathWriter;
  llvm::raw_ostream *m_infoFile;

  bool create_output_dir;
  SmallString<128> outputDirectory;

  unsigned casesGenerated;
  unsigned nextTestCaseID;
  std::string indentation;
  unsigned m_pathsExplored; // number of paths explored so far
  pid_t pid_watchdog;

  // used for writing .ktest files
  int m_argc;
  char **m_argv;

  std::map<std::string,unsigned> terminationCounters;

public:
  PGKleeHandler(int argc, char **argv, ProgInfo &pi, const std::string &entry);
  ~PGKleeHandler();

  bool createOutputDir() const { return create_output_dir; }
  llvm::raw_ostream &getInfoStream() const override { return *m_infoFile; }
  unsigned getNumTestCases() const override { return casesGenerated; }

  unsigned getNumPathsExplored() { return m_pathsExplored; }
  void incPathsExplored() override { m_pathsExplored++; }

  void setInterpreter(Interpreter *i) override;

  void processTestCase(ExecutionState  &state) override;

  std::string toDataString(const std::vector<unsigned char> &data) const;

  std::string getOutputFilename(const std::string &filename) override;
  std::string getTestFilename(const std::string &prefix, const std::string &ext, unsigned id);

  std::ostream *openTestCaseFile(const std::string &prefix, unsigned testID);
  llvm::raw_fd_ostream *openTestFile(const std::string &prefix, const std::string &ext, unsigned id);
  llvm::raw_fd_ostream *openOutputFile(const std::string &filename, bool exclusive=false) override;

  std::string getTypeName(const Type *Ty) const override;

  bool resetWatchDogTimer() const override;
  void setWatchDog(pid_t pid)     { pid_watchdog = pid; }

  // load a .path file
  static void loadPathFile(std::string name,
                           std::vector<bool> &buffer);

  static void getKTestFilesInDir(std::string directoryPath,
                                 std::vector<std::string> &results);

  static std::string getRunTimeLibraryPath(const char *argv0);

  void incTermination(const std::string &message) override;
  void getTerminationMessages(std::vector<std::string> &messages) override;
  unsigned getTerminationCount(const std::string &message) override;

};

PGKleeHandler::PGKleeHandler(int argc, char **argv, ProgInfo &pi, const std::string &entry)
  : m_pathWriter(nullptr),
    m_symPathWriter(nullptr),
    m_infoFile(nullptr),
    create_output_dir(false),
    outputDirectory(),
    casesGenerated(0),
    nextTestCaseID(1),
    indentation(""),
    m_pathsExplored(0),
    pid_watchdog(0),
    m_argc(argc),
    m_argv(argv) {

  // create output directory (OutputDir or "klee-out")
  outputDirectory = "klee-out";
  if (!OutputCreate.empty()) {
    create_output_dir = true;
    outputDirectory = OutputCreate;
  } else if (!OutputAppend.empty()) {
    outputDirectory = OutputAppend;
  }

  if (StartCaseID < 0) {
    // set default starting test case identifier
    if (!entry.empty()) {
      unsigned fnID = pi.getFnID(entry);
      if (fnID > 0) {
        nextTestCaseID = 100000 * fnID;
      }
    }

  } else {
    // assign explicit number
    nextTestCaseID = (unsigned) StartCaseID;
  }

  boost::filesystem::path p(outputDirectory.str());
  if (create_output_dir) {
    // create an empty directory
    boost::filesystem::remove_all(p);
    boost::filesystem::create_directories(p);
  } else {

    // error if the directory does not exist
    if (!boost::filesystem::exists(p)) {
      klee_error("append output directory does not exist");
    } else {

      // find the next available test id
      bool done = false;
      while (!done) {

        // find the next missing test case id.
        std::string testname = getOutputFilename(getTestFilename("test", "json", nextTestCaseID));
        std::string failname = getOutputFilename(getTestFilename("fail", "json", nextTestCaseID));
        boost::filesystem::path testfile(testname);
        boost::filesystem::path failfile(failname);
        if (boost::filesystem::exists(testfile) || boost::filesystem::exists(failfile)) {
          ++nextTestCaseID;
        } else {
          done = true;
        }
      }
    }
  }

  klee_message("output directory is \"%s\"", outputDirectory.c_str());

  // initialize error handling
  std::string prefix = OutputPrefix;
  if (prefix.empty()) {
    prefix = entry;
  }

  init_error_handling(outputDirectory.c_str(), prefix.c_str());

  // specialize info name for specialized entry points.
  std::string ifilename = "info.txt";
  if (!prefix.empty()) {
    ifilename = prefix + '-' + ifilename;
  }

  // open info
  m_infoFile = openOutputFile(ifilename);

  if (IndentJson) indentation = "  ";
}

PGKleeHandler::~PGKleeHandler() {
  if (m_pathWriter) delete m_pathWriter;
  if (m_symPathWriter) delete m_symPathWriter;
  term_error_handling();
  delete m_infoFile;
}

std::string PGKleeHandler::getTypeName(const Type *Ty) const {

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
        std::stringstream ss;
        ss << 'i' << cast<IntegerType>(Ty)->getBitWidth();
        return ss.str();
      }
      case Type::FunctionTyID: return "function";
      case Type::StructTyID: {
        const StructType *STy = cast<StructType>(Ty);
        return STy->getName().str();
      }
      case Type::PointerTyID: {

        std::stringstream ss;
        const PointerType *PTy = cast<PointerType>(Ty);
        ss << getTypeName(PTy->getElementType());
        ss << '*';
        return ss.str();
      }
      case Type::ArrayTyID: {

        std::stringstream ss;
        const ArrayType *ATy = cast<ArrayType>(Ty);
        ss << '[' << ATy->getNumElements() << " x ";
        ss << getTypeName(ATy->getElementType());
        ss << ']';
        return ss.str();
      }
      case Type::VectorTyID: {
        std::stringstream ss;
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

void PGKleeHandler::setInterpreter(Interpreter *i) {

  InterpreterHandler::setInterpreter(i);

  if (WritePaths) {
    m_pathWriter = new TreeStreamWriter(getOutputFilename("paths.ts"));
    assert(m_pathWriter->good());
    i->setPathWriter(m_pathWriter);
  }

  if (WriteSymPaths) {
    m_symPathWriter = new TreeStreamWriter(getOutputFilename("symPaths.ts"));
    assert(m_symPathWriter->good());
    i->setSymbolicPathWriter(m_symPathWriter);
  }
}

std::string PGKleeHandler::getOutputFilename(const std::string &filename) {

  SmallString<128> path = outputDirectory;
  sys::path::append(path, filename);
  return path.str();
}

llvm::raw_fd_ostream *PGKleeHandler::openOutputFile(const std::string &filename, bool exclusive) {
  llvm::raw_fd_ostream *f;
  std::string Error;
  std::string path = getOutputFilename(filename);
#if LLVM_VERSION_CODE >= LLVM_VERSION(3,5)
  f = new llvm::raw_fd_ostream(path.c_str(), Error, llvm::sys::fs::F_None);
#else
  llvm::sys::fs::OpenFlags fs_options = llvm::sys::fs::F_Binary;
  if (exclusive) {
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

std::string PGKleeHandler::getTestFilename(const std::string &prefix, const std::string &ext, unsigned id) {
  std::stringstream filename;
  filename << prefix << std::setfill('0') << std::setw(10) << id << '.' << ext;
  return filename.str();
}

llvm::raw_fd_ostream *PGKleeHandler::openTestFile(const std::string &prefix, const std::string &ext, unsigned id) {
  return openOutputFile(getTestFilename(prefix, ext, id));
}

std::ostream *PGKleeHandler::openTestCaseFile(const std::string &prefix, unsigned testID) {

  std::ofstream *result = nullptr;
  std::string filename = getOutputFilename(getTestFilename(prefix, "json", testID));
  result = new std::ofstream(filename);
  if (result != nullptr) {
    if (!result->is_open()) {
      delete result;
      result = nullptr;
    }
  }
  return result;
}

std::string PGKleeHandler::toDataString(const std::vector<unsigned char> &data) const {

  std::stringstream bytes;
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
void PGKleeHandler::processTestCase(ExecutionState &state) {

  Interpreter *i = getInterpreter();

  if (i != nullptr && !NoOutput) {

    // select the next test id for this function
    unsigned testID = nextTestCaseID++;
    double start_time = util::getWallTime();
    std::string prefix = "test";
    std::ostream *kout = openTestCaseFile(prefix, testID);
    if (kout != nullptr) {

      // construct the json object representing the test case
      Json::Value root = Json::objectValue;
      root["entryFn"] = state.name;
      root["testID"] = testID;
      root["argC"] = m_argc;
      root["lazyAllocationCount"] = state.lazyAllocationCount;
      root["maxLoopIteration"] = state.maxLoopIteration;
      root["maxLoopForks"] = state.maxLoopForks;
      root["maxLazyDepth"] = state.maxLazyDepth;
      root["startingMarker"] = state.startingMarker;
      root["endingMarker"] = state.endingMarker;
      root["unconstraintFlags"] = state.getUnconstraintFlags().to_string();
      root["unconstraintDescription"] = flags_to_string(state.getUnconstraintFlags());
      root["kleeRevision"] = KLEE_BUILD_REVISION;
      root["status"] = state.get_status();
      if (state.instFaulting != nullptr) {
        root["instFaulting"] = state.instFaulting->info->assemblyLine;
      }
      root["message"] = state.terminationMessage;

      // calculate a measure of unconstraint for this state
      double unconstraintMetric = 0.0;
      if (state.allBranchCounter != 0) {
        unconstraintMetric = ((double) state.unconBranchCounter) / ((double) state.allBranchCounter);
      }
      root["unconstraintMetric"] = unconstraintMetric;

      // store the path condition
      std::string constraints;
      i->getConstraintLog(state, constraints, Interpreter::SMTVARS);
      root["pathConditionVars"] = constraints;

      std::stringstream args;
      for (int index = 0; index < m_argc; ++index) {
        if (index > 0) args << ' ';
        args << '\'' << m_argv[index] << '\'';
      }
      root["argV"] = args.str();

      // store the marker trace
      Json::Value &path = root["markerTrace"] = Json::arrayValue;
      for (auto itr = state.trace.begin(), end = state.trace.end(); itr != end; ++itr) {
        path.append(std::to_string(itr->first) + ':' + std::to_string(itr->second));
      }

      // store the selection paths
      Json::Value &select = root["selectedPaths"] = Json::objectValue;
      for (auto itr = state.selected_paths.begin(), end = state.selected_paths.end(); itr != end; ++itr) {
        Json::Value &fn = select[std::to_string(itr->first)] = Json::arrayValue;
        for (auto path : itr->second) {
          fn.append(path);
        }
      }

      Json::Value &covered = root["coveredPaths"] = Json::objectValue;
      for (auto itr = state.itraces.begin(), end = state.itraces.end(); itr != end; ++itr) {
        Json::Value &fn = covered[std::to_string(itr->first)] = Json::arrayValue;
        for (auto path : itr->second) {
          fn.append(path);
        }
      }

      if (!NoSolution) {

        std::vector<SymbolicSolution> out;
        if (!i->getSymbolicSolution(state, out)) {
          klee_warning("unable to get symbolic solution, losing test case");
        }
        Json::Value &objects = root["objects"] = Json::arrayValue;
        for (auto itrObj = out.begin(), endObj = out.end(); itrObj != endObj; ++itrObj) {

          auto &test = *itrObj;
          const MemoryObject *mo = test.first;
          std::vector<unsigned char> &data = test.second;

          Json::Value obj = Json::objectValue;
          obj["name"] = mo->name;
          obj["kind"] = mo->getKindAsStr();
          obj["count"] = mo->count;
          const ObjectState *os = state.addressSpace.findObject(mo);
          std::string type = "?unknown?";
          if (os != nullptr) {
            type = getTypeName(os->getLastType());
          }
          obj["type"] = type;

          // scale to 32 or 64 bits
          unsigned ptr_width = (Context::get().getPointerWidth() / 8);
          std::vector<unsigned char> addr;
          unsigned char *addrBytes = ((unsigned char *) &(test.first->address));
          for (unsigned index = 0; index < ptr_width; ++index, ++addrBytes) {
            addr.push_back(*addrBytes);
          }
          obj["addr"] = toDataString(addr);
          obj["data"] = toDataString(data);

          objects.append(obj);
        }
      }

      // only if needed
      if (!NoAddressSpace && !NoSolution) {

        // dump details of the state address space
        root["addressSpace"] = Json::arrayValue;
        Json::Value &addrSpace = root["addressSpace"];

        std::vector<ObjectPair> listOPs;
        state.addressSpace.getMemoryObjects(listOPs);
        for (const auto pr : listOPs) {

          const MemoryObject *mo = pr.first;
          const ObjectState *os = pr.second;

          Json::Value obj = Json::objectValue;
          obj["id"] = mo->id;
          obj["name"] = mo->name;
          obj["kind"] = mo->getKindAsStr();
          obj["count"] = mo->count;
          obj["physical_size"] = mo->size;
          obj["visible_size"] = os->visible_size;
          obj["type"] = getTypeName(os->getLastType());
          obj["type_history"] = Json::arrayValue;
          for (auto itr = os->types.rbegin(), end = os->types.rend(); itr != end; ++itr) {
            obj["type_history"].append(getTypeName(*itr));
          }

          // scale to 32 or 64 bits
          unsigned ptr_width = (Context::get().getPointerWidth() / 8);
          std::vector<unsigned char> addr;
          unsigned char *addrBytes = ((unsigned char *) &(mo->address));
          for (unsigned index = 0; index < ptr_width; ++index, ++addrBytes) {
            addr.push_back(*addrBytes);
          }
          obj["addr"] = toDataString(addr);

          addrSpace.append(obj);
        }
      }

      // write the constructed json object to file
      Json::StreamWriterBuilder builder;
      builder["commentStyle"] = "None";
      builder["indentation"] = indentation;
      std::unique_ptr<Json::StreamWriter> writer(builder.newStreamWriter());

      writer.get()->write(root, kout);
      *kout << std::endl;

      kout->flush();
      delete kout;
      state.isProcessed = true;
      ++casesGenerated;
    } else {
      klee_warning("unable to write output test case, losing it");
    }

    if (m_pathWriter) {
      std::vector<unsigned char> concreteBranches;
      m_pathWriter->readStream(i->getPathStreamID(state), concreteBranches);
      llvm::raw_fd_ostream *f = openTestFile("test", "path", testID);
      for (auto I = concreteBranches.begin(), E = concreteBranches.end(); I != E; ++I) {
        *f << *I << "\n";
      }
      delete f;
    }

    if (WriteCVCs) {
      // FIXME: If using Z3 as the core solver the emitted file is actually
      // SMT-LIBv2 not CVC which is a bit confusing
      std::string constraints;
      i->getConstraintLog(state, constraints, Interpreter::STP);
      llvm::raw_ostream *f = openTestFile("test", "cvc", testID);
      *f << constraints;
      delete f;
    }

    if (WriteSMT2s) {
      std::string constraints;
        i->getConstraintLog(state, constraints, Interpreter::SMTLIB2);
        llvm::raw_ostream *f = openTestFile("test", "smt2", testID);
        *f << constraints;
        delete f;
    }

    if (m_symPathWriter) {
      std::vector<unsigned char> symbolicBranches;
      m_symPathWriter->readStream(i->getSymbolicPathStreamID(state), symbolicBranches);
      llvm::raw_fd_ostream *f = openTestFile("test", "sym.path", testID);
      for (auto I = symbolicBranches.begin(), E = symbolicBranches.end(); I!=E; ++I) {
        *f << *I << "\n";
      }
      delete f;
    }

    if (WriteCov) {
      std::map<const std::string*, std::set<unsigned> > cov;
      i->getCoveredLines(state, cov);
      llvm::raw_ostream *f = openTestFile("test", "cov", testID);
      for (auto it = cov.begin(), ie = cov.end(); it != ie; ++it) {
        for (auto it2 = it->second.begin(), ie2 = it->second.end(); it2 != ie2; ++it2)
          *f << *it->first << ":" << *it2 << "\n";
      }
      delete f;
    }

    if (WriteTestInfo) {
      double elapsed_time = util::getWallTime() - start_time;
      llvm::raw_ostream *f = openTestFile("test", "info", testID);
      *f << "Time to generate test case: "
         << elapsed_time << "s\n";
      delete f;
    }
  }
}

  // load a .path file
void PGKleeHandler::loadPathFile(std::string name,
                                     std::vector<bool> &buffer) {
  std::ifstream f(name.c_str(), std::ios::in | std::ios::binary);

  if (!f.good())
    assert(0 && "unable to open path file");

  while (f.good()) {
    unsigned value;
    f >> value;
    buffer.push_back(!!value);
    f.get();
  }
}

void PGKleeHandler::getKTestFilesInDir(std::string directoryPath,
                                     std::vector<std::string> &results) {
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  error_code ec;
#else
  std::error_code ec;
#endif
  for (llvm::sys::fs::directory_iterator i(directoryPath, ec), e; i != e && !ec;
       i.increment(ec)) {
    std::string f = (*i).path();
    if (f.substr(f.size()-6,f.size()) == ".ktest") {
          results.push_back(f);
    }
  }

  if (ec) {
    llvm::errs() << "ERROR: unable to read output directory: " << directoryPath
                 << ": " << ec.message() << "\n";
    exit(1);
  }
}

std::string PGKleeHandler::getRunTimeLibraryPath(const char *argv0) {
  // allow specifying the path to the runtime library
  const char *env = getenv("KLEE_RUNTIME_LIBRARY_PATH");
  if (env) {
    return std::string(env);
  }

  if (strlen(KLEE_INSTALL_RUNTIME_DIR) > 0) {
    return std::string(KLEE_INSTALL_RUNTIME_DIR);
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

bool PGKleeHandler::resetWatchDogTimer() const {

  // signal the watchdog process
  if (pid_watchdog != 0) {
    kill(pid_watchdog, SIGUSR1);
    return true;
  }
  return false;
}

void PGKleeHandler::incTermination(const std::string &message) {
  ++terminationCounters[message];
}

void PGKleeHandler::getTerminationMessages(std::vector<std::string> &messages) {

  for (const auto &pr : terminationCounters) {
    messages.push_back(pr.first);
  }
}

unsigned PGKleeHandler::getTerminationCount(const std::string &message) {
  return terminationCounters[message];
}

//===----------------------------------------------------------------------===//
// main Driver function
//
static std::string strip(std::string &in) {
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

  AllocaInst* argcPtr =
    new AllocaInst(oldArgc->getType(), "argcPtr", firstInst);
  AllocaInst* argvPtr =
    new AllocaInst(oldArgv->getType(), "argvPtr", firstInst);

  /* Insert void klee_init_env(int* argc, char*** argv) */
  std::vector<const Type*> params;
  LLVMContext &ctx = mainModule->getContext();
  params.push_back(Type::getInt32Ty(ctx));
  params.push_back(Type::getInt32Ty(ctx));
  Function* initEnvFn =
    cast<Function>(mainModule->getOrInsertFunction("klee_init_env",
                                                   Type::getVoidTy(ctx),
                                                   argcPtr->getType(),
                                                   argvPtr->getType(),
                                                   NULL));
  assert(initEnvFn);
  std::vector<Value*> args;
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

std::string calcChecksum(const std::string &filename){

  std::string result;
  std::ifstream infile(filename, std::ifstream::binary);
  if (infile.is_open()) {

    SHA256_CTX sha256;
    char buffer[1024];

    SHA256_Init(&sha256);
    while (infile.read(buffer, sizeof(buffer))) {
      std::streamsize count = infile.gcount();
      if (count > 0) SHA256_Update(&sha256, buffer, count);
    }

    std::vector<unsigned char> hash(SHA256_DIGEST_LENGTH);
    SHA256_Final(hash.data(), &sha256);
    boost::algorithm::hex(hash.begin(), hash.end(), std::back_inserter(result));
  }
  return result;
}


#define NELEMS(array) (sizeof(array)/sizeof(array[0]))

void externalsAndGlobalsCheck(const Module *m, bool emit_warnings) {
  std::set<std::string> modelled(modelledExternals,
                                 modelledExternals+NELEMS(modelledExternals));
  std::set<std::string> dontCare(dontCareExternals,
                                 dontCareExternals+NELEMS(dontCareExternals));

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

  std::set<std::string> extFunctions;
  std::set<std::string> extGlobals;

  // get a list of functions declared, but not defined
  for (Module::const_iterator fnIt = m->begin(), fn_ie = m->end(); fnIt != fn_ie; ++fnIt) {
    if (fnIt->isDeclaration() && !fnIt->use_empty()) {
      std::string name = fnIt->getName();
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

static void interrupt_handle() {
  if (!interrupted && theInterpreter) {
    llvm::errs() << "KLEE: ctrl-c detected, requesting interpreter to halt.\n";
    halt_execution();
    sys::SetInterruptFunction(interrupt_handle);
  } else {
    llvm::errs() << "KLEE: ctrl-c detected, exiting.\n";
    exit(1);
  }
  interrupted = true;
}

static void interrupt_handle_watchdog() {
  // just wait for the child to finish
}

// returns the end of the string put in buf
static char *format_tdiff(char *buf, long seconds)
{
  assert(seconds >= 0);

  long minutes = seconds / 60;  seconds %= 60;
  long hours   = minutes / 60;  minutes %= 60;
  long days    = hours   / 24;  hours   %= 24;

  buf = strrchr(buf, '\0');
  if (days > 0) buf += sprintf(buf, "%ld days, ", days);
  buf += sprintf(buf, "%02ld:%02ld:%02ld", hours, minutes, seconds);
  return buf;
}

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

  std::string uclibcLib = "klee-uclibc";
  std::string extension = ".bca";
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
  mainModule->getOrInsertFunction("__uClibc_main",
                                  FunctionType::get(Type::getVoidTy(ctx),
                                               std::vector<LLVM_TYPE_Q Type*>(),
                                                    true));

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
    const std::string &name = f->getName();
    if (name[0]=='\01') {
      unsigned size = name.size();
      if (name[size-2]=='6' && name[size-1]=='4') {
        std::string unprefixed = name.substr(1);

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
  Function *userMainFn = mainModule->getFunction(UserMain);
  assert(userMainFn && "unable to get user main");
  Function *uclibcMainFn = mainModule->getFunction("__uClibc_main");
  assert(uclibcMainFn && "unable to get uclibc main");

  const FunctionType *ft = uclibcMainFn->getFunctionType();
  assert(ft->getNumParams() == 7);

  std::string new_entry = "__user_" + UserMain;
  UserMain = new_entry;

  std::vector<LLVM_TYPE_Q Type*> fArgs;
  fArgs.push_back(ft->getParamType(1)); // argc
  fArgs.push_back(ft->getParamType(2)); // argv
  Function *stub = Function::Create(FunctionType::get(Type::getInt32Ty(ctx), fArgs, false),
                                    GlobalVariable::ExternalLinkage,
                                    UserMain,
                                    mainModule);
  BasicBlock *bb = BasicBlock::Create(ctx, "entry", stub);

  std::vector<llvm::Value*> args;
  args.push_back(llvm::ConstantExpr::getBitCast(userMainFn, ft->getParamType(0)));
  args.push_back(static_cast<Argument *>(stub->arg_begin())); // argc
  args.push_back(static_cast<Argument *>(++stub->arg_begin())); // argv
  args.push_back(Constant::getNullValue(ft->getParamType(3))); // app_init
  args.push_back(Constant::getNullValue(ft->getParamType(4))); // app_fini
  args.push_back(Constant::getNullValue(ft->getParamType(5))); // rtld_fini
  args.push_back(Constant::getNullValue(ft->getParamType(6))); // stack_end
  CallInst::Create(uclibcMainFn, args, "", bb);

  new UnreachableInst(ctx, bb);

  // and trivialize functions we will never use
  std::set<std::string> trivialize_fns {
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

  klee_message("NOTE: Using klee-uclibc : %s", uclibcBCA.c_str());
  return mainModule;
}
#endif

void accumulate_transitive_closure(const std::map<std::string,std::set<std::string> > &map_callees,
                                   const std::string &fn,
                                   std::set<std::string> &callees) {

  const auto &itr = map_callees.find(fn);
  if (itr != map_callees.end()) {
    for (const auto &child : itr->second) {
      if (callees.count(child) == 0) {
        callees.insert(child);
        accumulate_transitive_closure(map_callees, child, callees);
      }
    }
  }
}

void load_prog_info(Json::Value &root, ProgInfo &progInfo) {

  // complete progInfo from json structure

  // get a list of non-const global variables defined in this module
  std::set<std::string> global_vars;
  Json::Value &globalRoot = root["globals"];
  Json::Value::Members gbls = globalRoot.getMemberNames();
  for (const auto gbl : gbls) {
    if (!globalRoot[gbl]["type"]["isConst"].asBool()) {
      global_vars.insert(gbl);
    }
  }

  Json::Value &chksum = root["checksum"];
  if (chksum.isString()) progInfo.setChecksum(chksum.asString());

  // need a map of callees per function
  std::map<std::string,std::set<std::string> > map_callees;

  Json::Value &fnsRoot = root["functions"];
  Json::Value::Members fns = fnsRoot.getMemberNames();
  for (const auto &fn : fns) {

    // find the constant function params
    Json::Value &fnRoot = fnsRoot[fn];
    Json::Value &params = fnRoot["params"];
    unsigned id = fnRoot["fnID"].asUInt();
    progInfo.setFnID(fn, id);

    if (params.isArray()) {
      for (unsigned index = 0, end = params.size(); index < end; ++index) {

        Json::Value &param = params[index];
        if (!param["isOutput"].asBool()) {
          Json::Value &type = param["type"];
          if (type.isMember("isConst") && type["isConst"].asBool()) {
            progInfo.setConstParam(fn, index);
          }
        }
      }
    }

    // get all of the functions direct callees
    Json::Value &callTargets = fnRoot["callTargets"];
    if (callTargets.isArray()) {
      for (unsigned index = 0, end = callTargets.size(); index < end; ++index) {
        Json::Value &target = callTargets[index];
        map_callees[fn].insert(target.asString());
      }
    }

    // find the referenced global variables
    Json::Value &globals = fnRoot["globalRefs"];
    if (globals.isArray()) {
      for (unsigned index = 0, end = globals.size(); index < end; ++index) {
        Json::Value &global = globals[index];
        if (global["isInput"].asBool()) {
          std::string name = global["name"].asString();
          if (global_vars.count(name) > 0) {
            progInfo.setGlobalInput(fn, name);
          }
        }
        if (global["isOutput"].asBool()) {
          std::string name = global["name"].asString();
          if (global_vars.count(name) > 0) {
            progInfo.setOutput(fn, name);
          }
        }
      }
    }

    // add the markers
    Json::Value &markers = fnRoot["marks"];
    if (markers.isArray()) {
      for (unsigned index = 0, end = markers.size(); index < end; ++index) {
        Json::Value &marker = markers[index];
        progInfo.add_marker(fn, marker.asUInt());
      }
    }

    // then finally, add the m2m paths
    Json::Value &m2m_paths = fnRoot["m2m_paths"];
    if (m2m_paths.isArray()) {
      for (unsigned index1 = 0, end1 = m2m_paths.size(); index1 < end1; ++index1) {
        Json::Value &path = m2m_paths[index1];
        if (path.isArray()) {
          std::stringstream ss;
          ss << '.';
          for (unsigned index2 = 0, end2 = path.size(); index2 < end2; ++index2) {
            Json::Value &marker = path[index2];
            ss << marker.asUInt() << '.';
          }
          progInfo.add_m2m_path(fn, ss.str());
        }
      }
    }
  }

  // now that we have a map of direct callees, we do a dfs to find all reachable callees
  for (const auto &itr : map_callees) {
    const std::string &fn = itr.first;
    std::set<std::string> callees;
    accumulate_transitive_closure(map_callees, fn, callees);

    progInfo.setReachableFn(fn, fn);
    for (const auto &callee : callees) {
      progInfo.setReachableFn(fn, callee);
    }
  }

  // get the prototypes, if that's all we have
  Json::Value &protosRoot = root["prototypes"];
  Json::Value::Members protos = protosRoot.getMemberNames();
  for (const auto fn : protos) {

    // find the constant function params
    Json::Value &fnRoot = protosRoot[fn];
    Json::Value &params = fnRoot["params"];
    progInfo.setFnID(fn, 0);

    if (params.isArray()) {
      for (unsigned index = 0, end = params.size(); index < end; ++index) {

        Json::Value &param = params[index];
        if (!param["isOutput"].asBool()) {
          Json::Value &type = param["type"];
          if (type.isMember("isConst") && type["isConst"].asBool()) {
            progInfo.setConstParam(fn, index);
          }
        }
      }
    }
  }
}

volatile bool reset_watchdog_timer = false;

static void handle_usr1_signal(int signal, siginfo_t *dont_care, void *dont_care_either) {
  if (signal == SIGUSR1) {
    reset_watchdog_timer = true;
  }
}

void enumModuleFunctions(const Module *m, std::set<std::string> &names) {

  names.clear();
  for (auto itr = m->begin(), end = m->end(); itr != end; ++itr) {
    if (itr->isDeclaration() && !itr->use_empty()) {
      names.insert(itr->getName());
    }
  }
}

bool parseUnconstraintProgression(std::vector<Interpreter::ProgressionDesc> &progression, const std::string &str) {

  bool result = false;
  if (str.empty()) {
    // default progression
    UnconstraintFlagsT flags;
    if (UserMain == "main") {
      progression.emplace_back(600, flags);
    }
    flags.set(UNCONSTRAIN_GLOBAL_FLAG);
    progression.emplace_back(600, flags);
    flags.reset();
    flags.set(UNCONSTRAIN_LOCAL_FLAG);
    progression.emplace_back(60, flags);
    flags.reset();
    flags.set(UNCONSTRAIN_STUB_FLAG);
    progression.emplace_back(60, flags);
    result = true;
  } else {

    // parse out the progression phases
    std::vector<std::string> phases;
    boost::split(phases, str, [](char c){return c == ',';});
    for (auto phase: phases) {

      // loop through each phase in progression
      UnconstraintFlagsT flags;
      unsigned timeout = 60;

      // parse out the phase
      bool done = false;
      for (auto itr = phase.begin(), end = phase.end(); (!done) && itr != end; ++itr) {

        if (*itr == ':') {
          // rest of string is a unsigned timeout
          timeout = (unsigned) std::stoi(std::string(itr + 1, end));
          char suffix = (char) tolower(phase.back());
          if (suffix == 'm') {
            timeout *= 60;
          } else if (suffix == 'h') {
            timeout *= (60 * 60);
          }
          done = true;
        } else if (*itr == 'g') {
          flags.set(UNCONSTRAIN_GLOBAL_FLAG);
        } else if (*itr == 'l') {
          flags.set(UNCONSTRAIN_LOCAL_FLAG);
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

int main(int argc, char **argv, char **envp) {

  // used to find the beginning of the heap
  extern void *_end;

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();

  pid_t pid_watchdog = 0;
  if (Watchdog) {

    int pid = fork();
    if (pid<0) {
      klee_error("unable to fork watchdog");
    } else if (pid > 0) {
      reset_watchdog_timer = false;
//      klee_message("KLEE: WATCHDOG: watching %d", pid);
      sys::SetInterruptFunction(interrupt_handle_watchdog);

      // catch SIGUSR1
      struct sigaction sa;
      memset(&sa, 0, sizeof(sa));
      sigemptyset(&sa.sa_mask);
      sa.sa_flags = SA_NODEFER;
      sa.sa_sigaction = handle_usr1_signal;
      sigaction(SIGUSR1, &sa, nullptr);

      uint64_t heartbeat_timeout = HEARTBEAT_INTERVAL * 16;
      struct timespec tm;
      clock_gettime(CLOCK_MONOTONIC, &tm);
      uint64_t now = (uint64_t) tm.tv_sec;
      uint64_t nextStep = now + heartbeat_timeout;

      // Simple stupid code...
      while (true) {
        sleep(1);

        int status;
        int res = waitpid(pid, &status, WNOHANG);

        if (res < 0) {
          if (errno==ECHILD) { // No child, no need to watch but
                               // return error since we didn't catch
                               // the exit.
            klee_warning("KLEE: watchdog exiting (no child)");
            return 1;
          } else if (errno!=EINTR) {
            perror("watchdog waitpid");
            exit(1);
          }
        } else if (res==pid && WIFEXITED(status)) {
          return WEXITSTATUS(status);
        } else {

          clock_gettime(CLOCK_MONOTONIC, &tm);
          now = (uint64_t) tm.tv_sec;

          if (reset_watchdog_timer) {

            nextStep = now + heartbeat_timeout;
            reset_watchdog_timer = false;
          } else if (now > nextStep) {

            errs() << "KLEE: WATCHDOG: timer expired, attempting halt via INT\n";
            kill(pid, SIGINT);

            // Ideally this triggers a dump, which may take a while,
            // so try and give the process extra time to clean up.
            for (unsigned counter = 0; counter < 30; counter++) {
              sleep(1);
              res = waitpid(pid, &status, WNOHANG);
              if (res < 0) {
                return 1;
              } else if (res==pid && WIFEXITED(status)) {
                return WEXITSTATUS(status);
              }
            }
            errs() << "KLEE: WATCHDOG: kill(9)ing child (I did ask nicely)\n";
            kill(pid, SIGKILL);
            return 1; // what more can we do
          }
        }
      }

      return 0;
    }
  }

  sys::SetInterruptFunction(interrupt_handle);

  if (Watchdog) {
    // then this is the forked child
    pid_watchdog = getppid();
  }

  // Load the bytecode...
  std::string ErrorMsg;
  LLVMContext ctx;
  Module *mainModule = nullptr;
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  OwningPtr<MemoryBuffer> BufferPtr;
  error_code ec=MemoryBuffer::getFileOrSTDIN(InputFile.c_str(), BufferPtr);
  if (ec) {
    klee_error("error loading program '%s': %s", InputFile.c_str(),
               ec.message().c_str());
  }

  mainModule = getLazyBitcodeModule(BufferPtr.get(), ctx, &ErrorMsg);

  if (mainModule) {
    if (mainModule->MaterializeAllPermanently(&ErrorMsg)) {
      delete mainModule;
      mainModule = nullptr;
    }
  }
  if (!mainModule)
    klee_error("error loading program '%s': %s", InputFile.c_str(), ErrorMsg.c_str());
#else
  auto Buffer = MemoryBuffer::getFileOrSTDIN(InputFile.c_str());
  if (!Buffer)
    klee_error("error loading program '%s': %s", InputFile.c_str(),
               Buffer.getError().message().c_str());

  auto mainModuleOrError = getLazyBitcodeModule(Buffer->get(), ctx);

  if (!mainModuleOrError) {
    klee_error("error loading program '%s': %s", InputFile.c_str(),
               mainModuleOrError.getError().message().c_str());
  }
  else {
    // The module has taken ownership of the MemoryBuffer so release it
    // from the std::unique_ptr
    Buffer->release();
  }

  mainModule = *mainModuleOrError;
  if (auto ec = mainModule->materializeAllPermanently()) {
    klee_error("error loading program '%s': %s", InputFile.c_str(),
               ec.message().c_str());
  }
#endif

  ProgInfo progInfo;
  if (!ProgramInfo.empty()) {

    std::ifstream info;
    info.open(ProgramInfo);
    if (info.is_open()) {

      Json::Value root;
      info >> root;
      load_prog_info(root, progInfo);
    }
  }
  if (progInfo.empty()) {
    klee_error("program info json repository is required");
  }

  if (!progInfo.isChecksum(calcChecksum(InputFile))) {
    klee_error("program signature does not match info data");
  }

  if (WithPOSIXRuntime) {
    int r = initEnv(mainModule);
    if (r != 0)
      return r;
  }

  std::string LibraryDir = PGKleeHandler::getRunTimeLibraryPath(argv[0]);
 
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

    std::string posixLib = "libkleeRuntimePOSIX";
    Module::PointerSize width = mainModule->getPointerSize();
    if (width == Module::PointerSize::Pointer32) {
      posixLib += "-32";
    } else if (width == Module::PointerSize::Pointer64) {
      posixLib += "-64";
    }
    posixLib += ".bca";

    llvm::sys::path::append(Path, posixLib);
    klee_message("NOTE: Using model: %s", Path.c_str());
    mainModule = klee::linkWithLibrary(mainModule, Path.c_str());
    assert(mainModule && "unable to link with simple model");
  }

  std::vector<std::string>::iterator libs_it;
  std::vector<std::string>::iterator libs_ie;
  for (libs_it = LinkLibraries.begin(), libs_ie = LinkLibraries.end();
          libs_it != libs_ie; ++libs_it) {
    const char * libFilename = libs_it->c_str();
    klee_message("Linking in library: %s.\n", libFilename);
    mainModule = klee::linkWithLibrary(mainModule, libFilename);
  }
  // Get the desired main function.  klee_main initializes uClibc
  // locale and other data and then calls main.
  Function *mainFn = mainModule->getFunction(UserMain);

  // FIXME: Change me to std types.
  int pArgc;
  char **pArgv;
  char **pEnvp;
  if (Environ != "") {
    std::vector<std::string> items;
    std::ifstream f(Environ.c_str());
    if (!f.good())
      klee_error("unable to open --environ file: %s", Environ.c_str());
    while (!f.eof()) {
      std::string line;
      std::getline(f, line);
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
    std::string &arg = (i==0 ? InputFile : InputArgv[i-1]);
    unsigned size = arg.size() + 1;
    char *pArg = new char[size];

    std::copy(arg.begin(), arg.end(), pArg);
    pArg[size - 1] = 0;

    pArgv[i] = pArg;
  }

  // check if a starting block has pen appended to entrypoint function name
  unsigned starting_marker = 0;
  auto pos = EntryPoint.find(':');
  if (pos != std::string::npos) {
    starting_marker = std::stoi(EntryPoint.substr(pos + 1));
    EntryPoint.erase(pos);
  }

  PGKleeHandler *handler = new PGKleeHandler(pArgc, pArgv, progInfo, EntryPoint);
  handler->setWatchDog(pid_watchdog);

  void *heap_base = &_end;

  Interpreter::InterpreterOptions IOpts;
  IOpts.MakeConcreteSymbolic = MakeConcreteSymbolic;
  IOpts.createOutputDir = handler->createOutputDir();
  IOpts.heap_base = (void *) ((uint64_t) heap_base);
  if (!parseUnconstraintProgression(IOpts.progression, Progression)) {
    klee_error("failed to parse unconstraint progression: %s", Progression.c_str());
  }
  IOpts.pinfo = &progInfo;
  IOpts.verbose = Verbose;
  IOpts.mode = ExecMode;

  if (!SkipStartingBlocks.empty()) {

    // parse list of block identifiers
    std::vector<std::string> blocks;
    boost::split(blocks, SkipStartingBlocks, boost::is_any_of(", "));
    for (const auto &block : blocks) {
      IOpts.skipBlocks.push_back((unsigned) stoi(block));
    }
  }

  theInterpreter = Interpreter::createLocal(ctx, IOpts, handler);
  handler->setInterpreter(theInterpreter);

  for (int i=0; i<argc; i++) {
    handler->getInfoStream() << argv[i] << (i+1<argc ? " ":"\n");
  }
  handler->getInfoStream() << "PID: " << getpid() << "\n";

  Interpreter::ModuleOptions MOpts;

  MOpts.LibraryDir = LibraryDir;
  MOpts.EntryPoint = UserMain;
  MOpts.Optimize = OptimizeModule;
  MOpts.CheckDivZero = CheckDivZero;
  MOpts.CheckOvershift = CheckOvershift;
  MOpts.OutputStaticAnalysis = handler->createOutputDir();

  const Module *finalModule = theInterpreter->setModule(mainModule, MOpts);

  externalsAndGlobalsCheck(finalModule, handler->createOutputDir());

  char buf[256];
  time_t t[2];
  t[0] = time(NULL);
  strftime(buf, sizeof(buf), "Started: %Y-%m-%d %H:%M:%S\n", localtime(&t[0]));
  handler->getInfoStream() << buf;
  handler->getInfoStream().flush();

  if (RunInDir != "") {
    int res = chdir(RunInDir.c_str());
    if (res < 0) {
      klee_error("Unable to change directory to: %s - %s", RunInDir.c_str(),
                 sys::StrError(errno).c_str());
    }
  }

  // select program entry point
  if (EntryPoint.empty()) {
    theInterpreter->runFunctionAsMain(mainFn, pArgc, pArgv, pEnvp);
  } else {
    std::string entryName = EntryPoint;
    Function *entryFn = mainModule->getFunction(entryName);
    if (entryFn != nullptr) {
      theInterpreter->runFunctionUnconstrained(entryFn, starting_marker);
    } else if (EntryPoint != "void") {
      klee_error("Unable to find function: %s", EntryPoint.c_str());
    }
  }

  t[1] = time(nullptr);
  strftime(buf, sizeof(buf), "Finished: %Y-%m-%d %H:%M:%S\n", localtime(&t[1]));
  handler->getInfoStream() << buf;

  strcpy(buf, "Elapsed: ");
  strcpy(format_tdiff(buf, t[1] - t[0]), "\n");
  handler->getInfoStream() << buf;

  // Free all the args.
  for (unsigned i=0; i<InputArgv.size()+1; i++)
    delete[] pArgv[i];
  delete[] pArgv;

  delete theInterpreter;
  theInterpreter = nullptr;

  uint64_t queries = *theStatisticManager->getStatisticByName("Queries");
  uint64_t queriesValid = *theStatisticManager->getStatisticByName("QueriesValid");
  uint64_t queriesInvalid = *theStatisticManager->getStatisticByName("QueriesInvalid");
  uint64_t queryCounterexamples = *theStatisticManager->getStatisticByName("QueriesCEX");
  uint64_t queryConstructs = *theStatisticManager->getStatisticByName("QueriesConstructs");
  uint64_t instructions = *theStatisticManager->getStatisticByName("Instructions");
  uint64_t forks = *theStatisticManager->getStatisticByName("Forks");

  handler->getInfoStream() << "KLEE: done: explored paths = " << 1 + forks << "\n";

  // Write some extra information in the info file which users won't
  // necessarily care about or understand.
  if (queries) {
    handler->getInfoStream()
      << "KLEE: done: avg. constructs per query = "
      << queryConstructs / queries << "\n";
  }
  handler->getInfoStream()
    << "KLEE: done: total queries = " << queries << "\n"
    << "KLEE: done: valid queries = " << queriesValid << "\n"
    << "KLEE: done: invalid queries = " << queriesInvalid << "\n"
    << "KLEE: done: query cex = " << queryCounterexamples << "\n";

  std::vector<std::string> termination_messages;
  handler->getTerminationMessages(termination_messages);
  for (const auto &message : termination_messages) {
    handler->getInfoStream() << "PG-KLEE: term: " << message << ": " << handler->getTerminationCount(message) << "\n";
  }

  std::stringstream stats;
  stats << "\n";
  stats << "KLEE: done: total instructions = "
        << instructions << "\n";
  stats << "KLEE: done: completed paths = "
        << handler->getNumPathsExplored() << "\n";
  stats << "KLEE: done: generated tests = "
        << handler->getNumTestCases() << "\n";

  // only display stats if output was appended (i.e. actual se was performed)
  if (EntryPoint != "void") {

    bool useColors = llvm::outs().is_displayed();
    if (useColors) llvm::outs().changeColor(llvm::raw_ostream::GREEN, true, false);
    llvm::outs() << stats.str();
    if (useColors) llvm::outs().resetColor();
  }
  handler->getInfoStream() << stats.str();

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  // FIXME: This really doesn't look right
  // This is preventing the module from being
  // deleted automatically
  BufferPtr.take();
#endif
  delete handler;

  return 0;
}
