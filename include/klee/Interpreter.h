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

#include <vector>
#include <string>
#include <map>
#include <set>
#include <bitset>

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
  InterpreterHandler() : interpreter(nullptr)  {}
  virtual ~InterpreterHandler() {}

  virtual void setInterpreter(Interpreter *i)  { interpreter = i; }
  virtual Interpreter *getInterpreter() { return interpreter; }

  virtual std::string getOutputFilename(const std::string &filename) = 0;
  virtual llvm::raw_fd_ostream *openOutputFile(const std::string &filename, bool exclusive=false) = 0;
  virtual llvm::raw_fd_ostream *openOutputAssembly() { return nullptr; }
  virtual llvm::raw_fd_ostream *openOutputBitCode() { return nullptr; }
  virtual std::string getModuleName() const { return ""; }
  virtual unsigned getNumTestCases() const { return 0; }

  virtual void incPathsExplored() {}
  virtual void incTermination(const std::string &message) {}
  virtual void getTerminationMessages(std::vector<std::string> &messages) {};
  virtual unsigned getTerminationCount(const std::string &message) { return 0; }
  virtual void processTestCase(ExecutionState &state) {};
  virtual bool resetWatchDogTimer() const { return false; }

private:
  Interpreter *interpreter;
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
  virtual void runMainConcrete(llvm::Function *fn, const std::vector<std::string> &args, llvm::Function *at) {}

  /*** Runtime options ***/

  virtual void setHaltExecution(bool value) = 0;

  virtual void setInhibitForking(bool value) = 0;

  virtual void prepareForEarlyExit() = 0;

  /*** State accessor methods ***/

  virtual unsigned getPathStreamID(const ExecutionState &state) = 0;

  virtual unsigned getSymbolicPathStreamID(const ExecutionState &state) = 0;

  virtual void getConstraintLog(const ExecutionState &state, std::string &res, LogType logFormat = LogType::STP) = 0;

  virtual bool getSymbolicSolution(const ExecutionState &state, std::vector<SymbolicSolution> &res) = 0;
  virtual bool getSymbolicSolution(const ExecutionState &state, std::vector<SymbolicSolution> &res, std::vector<ExprSolution> &exprs) {
    return getSymbolicSolution(state, res);
  }
  virtual bool getConcreteSolution(ExecutionState &state, std::vector<ConcreteSolution> &result) { return false; }

  virtual void getCoveredLines(const ExecutionState &state, std::map<const std::string*, std::set<unsigned> > &res) = 0;
  virtual KModule *getKModule() const { return nullptr; }
  virtual TraceType getTraceType() const { return TraceType::invalid; }
  virtual const UnconstraintFlagsT *getUnconstraintFlags() { return nullptr; }
};

} // End klee namespace

#endif
