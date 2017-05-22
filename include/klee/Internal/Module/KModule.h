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

#include "klee/Config/Version.h"
#include "klee/Interpreter.h"

#include <map>
#include <set>
#include <vector>

#include "llvm/ADT/SmallVector.h"

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

  struct KFunction {
    llvm::Function *function;

    unsigned numArgs, numRegisters;

    unsigned numInstructions;
    KInstruction **instructions;

    std::map<llvm::BasicBlock*, unsigned> basicBlockEntry;

    /// Whether instructions in this function should count as
    /// "coverable" for statistics and search heuristics.
    bool trackCoverage;

    // values collected from marked ir
    unsigned fnID;
    std::map<const llvm::BasicBlock*,unsigned> basicBlockMarker;
    llvm::SmallVector<std::pair<const llvm::BasicBlock*,const llvm::BasicBlock*>, 32> backedges;
    std::set<unsigned> majorMarkers;

  private:
    KFunction(const KFunction&);
    KFunction &operator=(const KFunction&);

    void recurseAllSimplePaths(const llvm::BasicBlock *bb,
                               std::set<const llvm::BasicBlock*> &visited,
                               std::vector<const llvm::BasicBlock*> &path,
                               m2m_paths_t &paths);

    void recurseAllSimpleCycles(const llvm::BasicBlock *bb,
                                const llvm::BasicBlock *dst,
                                std::set<const llvm::BasicBlock*> &visited,
                                std::vector<const llvm::BasicBlock*> &path,
                                m2m_paths_t &paths);

  public:
    explicit KFunction(llvm::Function*, KModule *);
    ~KFunction();

    unsigned getArgRegister(unsigned index) { return index; }
    bool isBackedge(const llvm::BasicBlock* src, const llvm::BasicBlock *dst) const;
    void addAllSimplePaths(m2m_paths_t &paths);
    void addAllSimpleCycles(const llvm::BasicBlock *bb, m2m_paths_t &paths);
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

    // Functions which are part of KLEE runtime
    std::set<const llvm::Function*> internalFunctions;

  private:
    // Mark function with functionName as part of the KLEE runtime
    void addInternalFunction(const char* functionName);

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
