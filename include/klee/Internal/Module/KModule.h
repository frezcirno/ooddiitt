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
#include "llvm/Analysis/LoopInfo.h"

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

  typedef std::pair<const llvm::BasicBlock*,const llvm::BasicBlock*> CFGEdge;
  typedef std::set<const llvm::BasicBlock*> BasicBlocks;

  class M2MPaths : public std::map<unsigned,std::set<std::string> > {
  public:
    size_t size() const { unsigned result = 0; for (auto itr : *this) { result += itr.second.size(); } return result; }
    bool empty() const {
      auto itr = this->begin();
      auto end = this->end();
      while (itr != end) {
        if (!itr->second.empty()) return false;
        itr++;
      }
      return true;
    }

    bool empty(unsigned fnID) {
      const auto &itr = this->find(fnID);
      if (itr != this->end()) {
        return itr->second.empty();
      }
      return true;
    }

    void clean() {
      auto itr = this->begin();
      auto end = this->end();
      while (itr != end) {
        if (itr->second.empty()) itr = erase(itr);
        else ++itr;
      }
    }

    void clear(unsigned fnID) {
      auto itr = this->begin();
      auto end = this->end();
      while (itr != end) {
        if (itr->first != fnID) itr = erase(itr);
        else ++itr;
      }
    }

    void extend(const M2MPaths &paths) {
      for (auto itr : paths) {
        unsigned fnID = itr.first;
        for (const std::string &path : itr.second) {
          (*this)[fnID].insert(path);
        }
      }
    }

    bool contains(unsigned fnID, const std::string &path) {
      auto itr = this->find(fnID);
      return (itr != end() && itr->second.count(path) > 0);
    }
  };

  struct KFunction {
    llvm::Function *function;

    unsigned numArgs;
    unsigned numRegisters;

    unsigned numInstructions;
    KInstruction **instructions;

    std::map<llvm::BasicBlock*, unsigned> basicBlockEntry;

    /// Whether instructions in this function should count as
    /// "coverable" for statistics and search heuristics.
    bool trackCoverage;

    unsigned fnID;
    const KFunction *annotationKFn;

    // loop analysis
    llvm::DominatorTree domTree;
    llvm::LoopInfo loopInfo;

    // marker info
// DELETEME:    std::map<const llvm::BasicBlock*,std::vector<unsigned> > mapMarkers;
// DELETEME:    std::map<unsigned, const llvm::BasicBlock*> mapBBlocks;

  private:
    KFunction(const KFunction&);

  public:
    explicit KFunction(llvm::Function*, KModule *);
    ~KFunction();

    unsigned getArgRegister(unsigned index) { return index; }
    bool isLoopHeader(const llvm::BasicBlock *bb) const
      { const auto *L = loopInfo.getLoopFor(bb); return (L && L->getHeader() == bb); }
    void getSuccessorBBs(const llvm::BasicBlock *bb, BasicBlocks &successors) const;
    void getPredecessorBBs(const llvm::BasicBlock *bb, BasicBlocks &predecessors) const;
// DELETEME:    void constructSortedBBlocks(std::deque<unsigned> &sortedList, const llvm::BasicBlock *entry = nullptr);
    bool reachesAnyOf(const llvm::BasicBlock *bb, const std::set<const llvm::BasicBlock*> &blocks) const;
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
    bool addInternalFunction(std::string name);
    void addInternalFunction(llvm::Function *fn) { internalFunctions.insert(fn); }
    bool isInternalFunction(const llvm::Function *fn) const
      { return (fn != nullptr) && (internalFunctions.find(fn) != internalFunctions.end()); }
    bool isModuleFunction(const llvm::Function *fn) const
      { return functionMap.find(const_cast<llvm::Function*>(fn)) != functionMap.end();}
//    bool isMarkedFunction(const llvm::Function *fn) const
//      { const auto &itr = functionMap.find(const_cast<llvm::Function*>(fn));
//        return (itr != functionMap.end() && itr->second->fnID != 0); }

    llvm::Function *getTargetFunction(llvm::Value *value) const;

    bool MatchSignature(const llvm::Function *fn, const llvm::Function *annotFn) const;
    bool MatchSignature(const llvm::Type *type, const llvm::Function *annotFn) const;
//    std::map<const llvm::Type*,KFunction*> mapTypeToAnnotation;

  private:

    // Functions which are part of KLEE runtime
    std::set<const llvm::Function*> internalFunctions;

  public:
    KModule(llvm::Module *_module);
    ~KModule();

    /// Initialize local data structures.
    //
    // FIXME: ihandler should not be here
    void prepare(const Interpreter::ModuleOptions &opts, InterpreterHandler *ihandler);
// DELETEME:    void prepareMarkers(const Interpreter::ModuleOptions &opts, InterpreterHandler *ih);
// DELETEME:    void EmitFunctionSet(llvm::raw_fd_ostream *os, std::string key, std::set<const llvm::Function*> fns, unsigned &counter_keys);

    /// Return an id for the given constant, creating a new one if necessary.
    unsigned getConstantID(llvm::Constant *c, KInstruction* ki);

    // marker function names
    bool isMarkerFnName(const std::string &name) const { return marker_fn_names.count(name) != 0; }
    bool isMarkerFn(const llvm::Function *fn) const { return marker_fns.count(fn) != 0; }

  private:
    const static std::set<std::string> marker_fn_names;
    std::set<const llvm::Function*> marker_fns;
};
} // End klee namespace

#endif
