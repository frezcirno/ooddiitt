//===-- KModule.h -----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_KMODULE_H
#define KLEE_KMODULE_H

#include "llvm/Analysis/Dominators.h"

#include "klee/Config/Version.h"
#include "klee/Interpreter.h"

#include <map>
#include <set>
#include <vector>

namespace llvm {
  class BasicBlock;
  class Constant;
  class Function;
  class Instruction;
  class Module;
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  class TargetData;
#else
  class DataLayout;
#endif
}

namespace klee {
  struct Cell;
  class Executor;
  class Expr;
  class InterpreterHandler;
  class InstructionInfoTable;
  struct KInstruction;
  class KModule;
  template<class T> class ref;

  typedef std::vector<unsigned> marker_path_t;
  typedef std::set<marker_path_t> marker_paths_t;
  typedef std::vector<const llvm::BasicBlock*> bb_path_t;
  typedef std::set<bb_path_t> bb_paths_t;
  typedef std::pair<const llvm::BasicBlock*,const llvm::BasicBlock*> CFGEdge;
  typedef std::set<const llvm::BasicBlock*> BasicBlocks;

  struct KLoopInfo {
    std::set<const llvm::BasicBlock*> bbs;
    std::set<const llvm::BasicBlock*> exits;
    KLoopInfo()                   { }
    KLoopInfo(const KLoopInfo &s) { bbs = s.bbs; exits = s.exits; }
  };

  struct KFunction {
    llvm::Function *function;

    unsigned numArgs, numRegisters;

    unsigned numInstructions;
    KInstruction **instructions;

    std::map<llvm::BasicBlock*, unsigned> basicBlockEntry;

    /// Whether instructions in this function should count as
    /// "coverable" for statistics and search heuristics.
    bool trackCoverage;

    unsigned fnID;

    // loop analysis
    std::map<const llvm::BasicBlock*,KLoopInfo> loopInfo;
    llvm::DominatorTree domTree;

    // marker info
    std::map<const llvm::BasicBlock*,std::vector<unsigned> > mapMarkers;
    std::set<unsigned> majorMarkers;
    marker_paths_t m2m_paths;

  private:
    KFunction(const KFunction&);
    KFunction &operator=(const KFunction&);

    void recurseAllSimplePaths(const llvm::BasicBlock *bb,
                               std::set<const llvm::BasicBlock*> &visited,
                               bb_path_t &path,
                               bb_paths_t &paths) const;

    void recurseAllSimpleCycles(const llvm::BasicBlock *bb,
                                const llvm::BasicBlock *dst,
                                std::set<const llvm::BasicBlock*> &visited,
                                bb_path_t &path,
                                bb_paths_t &paths) const;
    
    void translateBBPath2MarkerPath(const bb_path_t &bb_path, marker_path_t &marker_path) const;

  public:
    explicit KFunction(llvm::Function*, KModule *);
    ~KFunction();

    unsigned getArgRegister(unsigned index) { return index; }
    void findLoopHeaders();
    bool isLoopHeader(const llvm::BasicBlock *bb) const { return (loopInfo.find(bb) != loopInfo.end()); }
    bool isInLoop(const llvm::BasicBlock *hdr, const llvm::BasicBlock *bb) const;
    bool isLoopExit(const llvm::BasicBlock *hdr, const llvm::BasicBlock *bb) const;
    void getSuccessorBBs(const llvm::BasicBlock *bb, BasicBlocks &successors) const;
    void addAllSimplePaths(bb_paths_t &paths) const;
    void addAllSimpleCycles(const llvm::BasicBlock *bb, bb_paths_t &paths) const;
    void setM2MPaths(const bb_paths_t &bb_paths);
    bool isMajorMarker(unsigned marker) const        { return majorMarkers.find(marker) != majorMarkers.end(); }
  };


  class KConstant {
  public:
    /// Actual LLVM constant this represents.
    llvm::Constant* ct;

    /// The constant ID.
    unsigned id;

    /// First instruction where this constant was encountered, or NULL
    /// if not applicable/unavailable.
    KInstruction *ki;

    KConstant(llvm::Constant*, unsigned, KInstruction*);
  };


  class KModule {
  public:
    llvm::Module *module;
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
    llvm::TargetData *targetData;
#else
    llvm::DataLayout *targetData;
#endif
    
    // Some useful functions to know the address of
    llvm::Function *kleeMergeFn;

    // Our shadow versions of LLVM structures.
    std::vector<KFunction*> functions;
    std::map<llvm::Function*, KFunction*> functionMap;

    // Functions which escape (may be called indirectly)
    // XXX change to KFunction
    std::set<llvm::Function*> escapingFunctions;

    InstructionInfoTable *infos;

    std::vector<llvm::Constant*> constants;
    std::map<llvm::Constant*, KConstant*> constantMap;
    KConstant* getKConstant(llvm::Constant *c);

    Cell *constantTable;

    // Mark function with functionName as part of the KLEE runtime
    void addInternalFunction(std::string functionName);
    bool isInternalFunction(const llvm::Function *fn)
      { return internalFunctions.find(fn) != internalFunctions.end(); }

    // these functions will not be represented symbolically
    void addConcreteFunction(const llvm::Function *fn)
      { concreteFunctions.insert(fn); }
    void addConcreteFunction(std::string fnName);
    bool isConcreteFunction(const llvm::Function *fn)
      { return concreteFunctions.find(fn) != concreteFunctions.end(); }

    llvm::Function *getTargetFunction(llvm::Value *value) const;

  private:

    // Functions which should not be called symbolically
    std::set<const llvm::Function*> concreteFunctions;

    // Functions which are part of KLEE runtime
    std::set<const llvm::Function*> internalFunctions;

  public:
    KModule(llvm::Module *_module);
    ~KModule();

    /// Initialize local data structures.
    //
    // FIXME: ihandler should not be here
    void prepare(const Interpreter::ModuleOptions &opts, 
                 InterpreterHandler *ihandler);

    void prepareMarkers();

    /// Return an id for the given constant, creating a new one if necessary.
    unsigned getConstantID(llvm::Constant *c, KInstruction* ki);
  };
} // End klee namespace

#endif
