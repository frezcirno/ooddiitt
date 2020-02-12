//===-- Interpreter.h - Abstract Execution Engine Interface -----*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//===----------------------------------------------------------------------===//

#ifndef KLEE_INTERPRETER_H
#define KLEE_INTERPRETER_H

#include "TestCase.h"
#include "klee/util/CommonUtil.h"
#include "klee/util/Ref.h"
#include "klee/Expr.h"
#include <boost/filesystem.hpp>
#include <boost/algorithm/string.hpp>

#include <vector>
#include <string>
#include <map>
#include <set>
#include <bitset>
#include <klee/Internal/Support/ErrorHandling.h>

struct KTest;

namespace llvm {
class Function;
class LLVMContext;
class Module;
class raw_ostream;
class raw_fd_ostream;
}

namespace klee {
class ExecutionState;
class Interpreter;
class TreeStreamWriter;
class MemoryObject;
class KModule;
struct KInstruction;

typedef std::pair<const MemoryObject*,std::vector<unsigned char> > SymbolicSolution;
typedef std::pair<ref<Expr>,ref<ConstantExpr> > ExprSolution;
typedef SymbolicSolution ConcreteSolution;

#define HEARTBEAT_INTERVAL   (10)        // secs

#define UNCONSTRAIN_GLOBAL_FLAG (0)
#define UNCONSTRAIN_STUB_FLAG   (2)

enum class LogType
{
  STP, //.CVC (STP's native language)
  KQUERY, //.KQUERY files (kQuery native language)
  SMTLIB2, //.SMT2 files (SMTLIB version 2 files)
  SMTVARS  // part of SMT2 containing var declarations
};

enum class ExecModeID {
  none, // undefined
  prep,
  igen, // interpreter should execute module for cbert input generation
  rply, // interpreter should execute module for cbert replay
  irec  // record snapshot at a function entry
};

class UnconstraintFlagsT : public std::bitset<8> {

public:
  bool isStubCallees() const          { return test(UNCONSTRAIN_STUB_FLAG); }
  bool isUnconstrainGlobals() const   { return test(UNCONSTRAIN_GLOBAL_FLAG); }

  void setStubCallees(bool b = true)          { set(UNCONSTRAIN_STUB_FLAG, b); }
  void setUnconstrainGlobals(bool b = true)   { set(UNCONSTRAIN_GLOBAL_FLAG, b); }
};

inline std::string to_string(UnconstraintFlagsT flags) {

  const static std::vector< std::pair<unsigned,const std::string> > flag2name =  {
      std::make_pair(UNCONSTRAIN_GLOBAL_FLAG, "globals,"),
      std::make_pair(UNCONSTRAIN_STUB_FLAG, "stubs,")
  };

  std::string result("inputs,");
  for (auto p: flag2name) {
    if (flags.test(p.first)) {
      result += p.second;
    }
  }
  result.pop_back();
  return result;
}

class InterpreterHandler {
public:
  InterpreterHandler(const std::string &od, const std::string &_md_name, const std::string &_prefix);
  InterpreterHandler(const std::string &od, const std::string &_md_name);
  virtual ~InterpreterHandler() = default;

  virtual void setInterpreter(Interpreter *i)  { interpreter = i; }
  virtual Interpreter *getInterpreter() { return interpreter; }

  bool wasOutputCreated() const { return output_created; }
  std::string getTestFilename(const std::string &ext, unsigned id);
  std::string getOutputFilename(const std::string &filename);
  llvm::raw_fd_ostream *openOutputFile(const std::string &filename);
  std::string getModuleName() const { return module_name; }
  std::string getFileName() const { return file_name; }
  bool openTestCaseFile(std::ofstream &fout, unsigned test_id, std::string &name);

  llvm::raw_fd_ostream *openOutputAssembly() { return openOutputFile(getModuleName() + ".ll"); }
  llvm::raw_fd_ostream *openOutputBitCode()  { return openOutputFile(getModuleName() + ".bc"); }
  virtual unsigned getNumTestCases() const { return 0; }

  virtual void incPathsExplored() {}
  virtual void incTermination(const std::string &message) {}
  virtual void getTerminationMessages(std::vector<std::string> &messages) {};
  virtual unsigned getTerminationCount(const std::string &message) { return 0; }
  virtual void processTestCase(ExecutionState &state) {};
  virtual bool resetWatchDogTimer() const { return false; }

  void incCallCounter(const llvm::Function *fn) { call_counters[fn] += 1; }
  void getCallCounters(std::vector<std::pair<unsigned,const llvm::Function*> > &counters) const;

  static std::string getRunTimeLibraryPath(const char *argv0);

private:
  Interpreter *interpreter;
  boost::filesystem::path outputDirectory;
  bool output_created;
  std::string file_name;
  std::string module_name;
  std::string prefix;
  std::map<const llvm::Function*,unsigned> call_counters;
};

class Interpreter {
public:
  /// ModuleOptions - Module level options which can be set when
  /// registering a module with the interpreter.
  struct ModuleOptions {
    std::string LibraryDir;
    bool Optimize;
    bool CheckDivZero;
    bool CheckOvershift;

    ModuleOptions()
      : Optimize(false),
        CheckDivZero(false),
        CheckOvershift(false)
      {}
  };

  struct ProgressionDesc {
    unsigned timeout;
    UnconstraintFlagsT unconstraintFlags;

    explicit ProgressionDesc(unsigned t) : timeout(t) {}
    ProgressionDesc(unsigned t, const UnconstraintFlagsT &b) : timeout(t), unconstraintFlags(b) {}
  };

  /// InterpreterOptions - Options varying the runtime behavior during
  /// interpretation.
  struct InterpreterOptions {
    /// A frequency at which to make concrete reads return constrained
    /// symbolic values. This is used to test the correctness of the
    /// symbolic execution on concrete programs.
    unsigned MakeConcreteSymbolic;
    std::vector<ProgressionDesc> progression;
    ExecModeID mode;
    llvm::Function *userMain;
    llvm::Function *userSnapshot;
    void *user_mem_base;
    size_t user_mem_size;
    bool verbose;
    bool verify_constraints;
    std::vector<TestObject> *test_objs;
    TraceType trace;

    InterpreterOptions()
      : MakeConcreteSymbolic(0),
        mode(ExecModeID::none),
        userMain(nullptr),
        userSnapshot(nullptr),
        user_mem_base(nullptr),
        user_mem_size(0),
#ifdef _DEBUG
        verbose(true),
#else
        verbose(false),
#endif
        verify_constraints(false),
        test_objs(nullptr),
        trace(TraceType::invalid)
    {}
  };

protected:
  const InterpreterOptions interpreterOpts;

  Interpreter(const InterpreterOptions &_interpreterOpts) : interpreterOpts(_interpreterOpts) {};

public:
  virtual ~Interpreter() {};

  static Interpreter *create(llvm::LLVMContext &ctx,
                             const InterpreterOptions &_interpreterOpts,
                             InterpreterHandler *ih);

  static Interpreter *createLocal(llvm::LLVMContext &ctx,
                                  const InterpreterOptions &_interpreterOpts,
                                  InterpreterHandler *ih);

  const InterpreterOptions &getOptions() const { return interpreterOpts; }

  /// Register the module to be executed.
  ///
  /// \return The final module after it has been optimized, checks
  /// inserted, and modified for interpretation.
  virtual void bindModule(KModule *kmodule) = 0;


  // supply a tree stream writer which the interpreter will use
  // to record the concrete path (as a stream of '0' and '1' bytes).
  virtual void setPathWriter(TreeStreamWriter *tsw) = 0;

  // supply a tree stream writer which the interpreter will use
  // to record the symbolic path (as a stream of '0' and '1' bytes).
  virtual void setSymbolicPathWriter(TreeStreamWriter *tsw) = 0;

  // supply a test case to replay from. this can be used to drive the
  // interpretation down a user specified path. use null to reset.
  virtual void setReplayKTest(const struct KTest *out) = 0;

  // supply a list of branch decisions specifying which direction to
  // take on forks. this can be used to drive the interpretation down
  // a user specified path. use null to reset.
  virtual void setReplayPath(const std::vector<bool> *path) = 0;

  // supply a set of symbolic bindings that will be used as "seeds"
  // for the search. use null to reset.
  virtual void useSeeds(const std::vector<struct KTest *> *seeds) = 0;

  virtual void runFunctionAsMain(llvm::Function *f,
                                 int argc,
                                 char **argv,
                                 char **envp) = 0;

  virtual void runFunctionUnconstrained(llvm::Function *fn) { };
  virtual void runFunctionTestCase(const TestCase &test) {};
  virtual void runMainConcrete(llvm::Function *fn,
                               const std::vector<std::string> &args,
                               const std::vector<unsigned char> &stdin_buffer,
                               llvm::Function *at) {}

  /*** Runtime options ***/

  virtual void setHaltExecution(bool value) = 0;

  virtual void setInhibitForking(bool value) = 0;

  virtual void prepareForEarlyExit() = 0;

  /*** State accessor methods ***/

  virtual unsigned getPathStreamID(const ExecutionState &state) = 0;

  virtual unsigned getSymbolicPathStreamID(const ExecutionState &state) = 0;

  virtual void getConstraintLog(const ExecutionState &state, std::string &res, LogType logFormat) = 0;
  void getConstraintLog(const ExecutionState &state, std::string &res) { getConstraintLog(state, res, LogType::STP); }

  virtual bool getSymbolicSolution(const ExecutionState &state, std::vector<SymbolicSolution> &res) = 0;
  virtual bool getSymbolicSolution(const ExecutionState &state, std::vector<SymbolicSolution> &res, std::vector<ExprSolution> &exprs)
    { return getSymbolicSolution(state, res); }
  virtual bool getConcreteSolution(ExecutionState &state, std::vector<ConcreteSolution> &result, const std::set<MemKind> &kinds)
    { return false; }

  virtual void getCoveredLines(const ExecutionState &state, std::map<const std::string*, std::set<unsigned> > &res) = 0;
  virtual KModule *getKModule() const { return nullptr; }
  virtual TraceType getTraceType() const { return TraceType::invalid; }
  virtual const UnconstraintFlagsT *getUnconstraintFlags() { return nullptr; }
  virtual void log_warning(const std::string &msg) = 0;
  virtual void log_warning(const std::string &msg, ExecutionState &state) = 0;
  virtual void log_warning(const std::string &msg, ExecutionState &state, KInstruction *ki) = 0;
};

} // End klee namespace

#endif
