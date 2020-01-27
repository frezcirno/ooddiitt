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
#include "llvm/IR/Module.h"

#include "klee/Config/Version.h"
#include "klee/Interpreter.h"
#include "klee/Internal/System/Memory.h"
#include "klee/Internal/Support/ModuleUtil.h"

#include <map>
#include <set>
#include <vector>

namespace llvm {
  class BasicBlock;
  class Constant;
  class Function;
  class Instruction;
  class Module;
  class DataLayout;
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

    // loop analysis
    llvm::DominatorTree domTree;
    llvm::LoopInfo loopInfo;

    bool is_user;

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
    bool reachesAnyOf(const llvm::BasicBlock *bb, const std::set<const llvm::BasicBlock*> &blocks) const;
    bool isUser() const {return is_user; }
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
    void addInternalFunction(const llvm::Function *fn) { internalFunctions.insert(fn); }
    void addIntenalFunctions(const std::set<const llvm::Function*> &fns) {
      internalFunctions.insert(fns.begin(), fns.end());
    }
    bool isInternalFunction(const llvm::Function *fn) const
      { return (fn != nullptr) && (internalFunctions.find(fn) != internalFunctions.end()); }
    bool isModuleFunction(const llvm::Function *fn) const
      { return functionMap.find(const_cast<llvm::Function*>(fn)) != functionMap.end();}

    llvm::Function *getTargetFunction(llvm::Value *value) const;

  private:

    // Functions which are part of KLEE runtime
    std::set<const llvm::Function*> internalFunctions;

  public:
    KModule(llvm::Module *_module);
    ~KModule();

    llvm::Module *detachModule() { llvm::Module *m = module; module = nullptr; return m; }
    bool isPrepared() const { return module != nullptr && klee::isPrepared(module); }
    std::string getModuleIdentifier() const
      { std::string result; if (module) result = module->getModuleIdentifier(); return result; }

    /// Initialize local data structures.
    //
    // FIXME: ihandler should not be here
    void prepare();
    void transform(const Interpreter::ModuleOptions &opts,
                   const std::set<llvm::Function*> &module_fns,
                   const std::set<llvm::GlobalVariable*> &module_globals,
                   TraceType ttrace = TraceType::invalid,
                   MarkScope mscope = MarkScope::invalid);

    /// Return an id for the given constant, creating a new one if necessary.
    unsigned getConstantID(llvm::Constant *c, KInstruction* ki);

    std::pair<unsigned,unsigned> getMarker(const llvm::Function *fn, const llvm::BasicBlock *bb);
    void getMarkedFns(std::set<const llvm::Function*> &fns) {
      fns.clear();
      for (auto itr = mapFnMarkers.begin(), end = mapFnMarkers.end(); itr != end; ++itr) {
        fns.insert(itr->first);
      }
    }

    void getFnsOfType(const llvm::FunctionType *ft, std::set<const llvm::Function*> &fns) {
      auto itr = mapFnTypes.find(ft);
      if (itr != mapFnTypes.end()) {
        fns.insert(itr->second.begin(), itr->second.end());
      }
    }

    llvm::Type *getEquivalentType(const std::string &desc) const;
    void insertTypeDesc(llvm::Type *type)  {
      std::string test = to_string(type);
      mapTypeDescs[to_string(type)] = type;
      type = type->getPointerTo(0);
      mapTypeDescs[to_string(type)] = type;
    }

    bool isUserFunction(llvm::Function* fn) const {
      return user_fns.find(fn) != user_fns.end();
    }

    void getUserFunctions(std::set<llvm::Function*> &fns) const {
      fns.clear();
      for (auto itr = user_fns.begin(), end = user_fns.end(); itr != end; ++itr) fns.insert(*itr);
    }

    void getUserFunctions(std::set<std::string> &fns) const {
      fns.clear();
      for (auto itr = user_fns.begin(), end = user_fns.end(); itr != end; ++itr) fns.insert((*itr)->getName());
    }

    bool isUserGlobal(llvm::GlobalVariable* gb) const {
      return user_gbs.find(gb) != user_gbs.end();
    }

    void getUserGlobals(std::set<llvm::GlobalVariable*> &gbs) const {
      gbs.clear();
      for (auto itr = user_gbs.begin(), end = user_gbs.end(); itr != end; ++itr) gbs.insert(*itr);
    }

    void getUserGlobals(std::set<std::string> &gbs) {
      gbs.clear();
      for (auto itr = user_gbs.begin(), end = user_gbs.end(); itr != end; ++itr) gbs.insert((*itr)->getName());
    }

    unsigned getFunctionID(llvm::Function *fn) {
      auto itr = mapFnMarkers.find(fn);
      if (itr != mapFnMarkers.end()) return itr->second;
      else return 0;
    }

    TraceType getModuleTraceType() const { return module_trace; }

  private:
    std::map<const llvm::Function*,unsigned> mapFnMarkers;
    std::map<const llvm::BasicBlock*,unsigned> mapBBMarkers;
    std::map<const llvm::FunctionType*,std::set<const llvm::Function*> >mapFnTypes;
    std::map<std::string,llvm::Type*> mapTypeDescs;
    std::set<llvm::Function*> user_fns;
    std::set<llvm::GlobalVariable*> user_gbs;
    TraceType module_trace;
};

} // End klee namespace

#endif
