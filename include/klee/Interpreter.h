//===-- Interpreter.h - Abstract Execution Engine Interface -----*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//===----------------------------------------------------------------------===//

#ifndef KLEE_INTERPRETER_H
#define KLEE_INTERPRETER_H

#include "klee/Internal/System/ProgInfo.h"

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

typedef std::vector<unsigned> m2m_path_t;
typedef std::set<m2m_path_t> m2m_paths_t;
typedef std::pair<const MemoryObject*,std::vector<unsigned char> > SymbolicSolution;

#define HEARTBEAT_INTERVAL   (15)

#define UNCONSTRAIN_GLOBAL_FLAG (0)
#define UNCONSTRAIN_LOCAL_FLAG  (1)
#define UNCONSTRAIN_STUB_FLAG   (2)
typedef std::bitset<8> UnconstraintFlagsT;

class InterpreterHandler {
public:
  InterpreterHandler() {}
  virtual ~InterpreterHandler() {}

  virtual llvm::raw_ostream &getInfoStream() const = 0;

  virtual std::string getOutputFilename(const std::string &filename) = 0;
  virtual llvm::raw_fd_ostream *openOutputFile(const std::string &filename, bool exclusive=false) = 0;

  virtual void incPathsExplored() = 0;

  virtual void processTestCase(ExecutionState &state) = 0;

  virtual std::string getTypeName(const llvm::Type *Ty) const { return ""; }
  virtual bool resetWatchDogTimer() const { return false; }
  std::string to_string(UnconstraintFlagsT flags) const {

    const static std::vector< std::pair<unsigned,const std::string> > flag2name =  {
        std::make_pair(UNCONSTRAIN_GLOBAL_FLAG, "globals,"),
        std::make_pair(UNCONSTRAIN_LOCAL_FLAG, "locals,"),
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

};

class Interpreter {
public:
  /// ModuleOptions - Module level options which can be set when
  /// registering a module with the interpreter.
  struct ModuleOptions {
    std::string LibraryDir;
    std::string EntryPoint;
    bool Optimize;
    bool CheckDivZero;
    bool CheckOvershift;
    bool OutputStaticAnalysis;

    ModuleOptions()
      : Optimize(false),
        CheckDivZero(false),
        CheckOvershift(false),
        OutputStaticAnalysis(false)
      {}
  };

  enum LogType
  {
	  STP, //.CVC (STP's native language)
	  KQUERY, //.KQUERY files (kQuery native language)
	  SMTLIB2, //.SMT2 files (SMTLIB version 2 files)
      SMTVARS  // part of SMT2 containing var declarations
  };

  enum ExecModeID {
      none, // undefined
      zop,  // interpreter should execute module in zop mode
      fault // interpreter should execute module to find faults
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
    bool createOutputDir;
    void *heap_base;
    ProgInfo *pinfo;
    std::vector<ProgressionDesc> progression;
    ExecModeID mode;
    bool verbose;

    InterpreterOptions()
      : MakeConcreteSymbolic(0),
        createOutputDir(false),
        heap_base(nullptr),
        pinfo(nullptr),
        mode(Interpreter::zop),
        verbose(false)
    {}
  };

protected:
  const InterpreterOptions interpreterOpts;

  Interpreter(const InterpreterOptions &_interpreterOpts)
    : interpreterOpts(_interpreterOpts)
  {}

public:
  virtual ~Interpreter() {}

  static Interpreter *create(llvm::LLVMContext &ctx,
                             const InterpreterOptions &_interpreterOpts,
                             InterpreterHandler *ih);

  static Interpreter *createLocal(llvm::LLVMContext &ctx,
                                  const InterpreterOptions &_interpreterOpts,
                                  InterpreterHandler *ih);

  /// Register the module to be executed.  
  ///
  /// \return The final module after it has been optimized, checks
  /// inserted, and modified for interpretation.
  virtual const llvm::Module *setModule(llvm::Module *module, const ModuleOptions &opts) = 0;

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

  virtual void runFunctionUnconstrained(llvm::Function *f)          { };

  /*** Runtime options ***/

  virtual void setHaltExecution(bool value) = 0;

  virtual void setInhibitForking(bool value) = 0;

  virtual void prepareForEarlyExit() = 0;

  /*** State accessor methods ***/

  virtual unsigned getPathStreamID(const ExecutionState &state) = 0;

  virtual unsigned getSymbolicPathStreamID(const ExecutionState &state) = 0;
  
  virtual void getConstraintLog(const ExecutionState &state, std::string &res, LogType logFormat = STP) = 0;

  virtual bool getSymbolicSolution(const ExecutionState &state, std::vector<SymbolicSolution> &res) = 0;

  virtual void getCoveredLines(const ExecutionState &state,
                               std::map<const std::string*, std::set<unsigned> > &res) = 0;
};

} // End klee namespace

#endif
