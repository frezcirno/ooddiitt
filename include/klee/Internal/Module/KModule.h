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
//    llvm::DominatorTree domTree;
//    llvm::LoopInfo loopInfo;

    bool is_user;
    unsigned fnID;
    bool diff_added;
    bool diff_removed;
    bool diff_body;
    bool diff_sig;

  private:
    KFunction(const KFunction&);

  public:
    explicit KFunction(llvm::Function*, KModule *);
    ~KFunction();

    unsigned getArgRegister(unsigned index) { return index; }
//    bool isLoopHeader(const llvm::BasicBlock *bb) const
//      { const auto *L = loopInfo.getLoopFor(bb); return (L && L->getHeader() == bb); }
    void getSuccessorBBs(const llvm::BasicBlock *bb, BasicBlocks &successors) const;
    void getPredecessorBBs(const llvm::BasicBlock *bb, BasicBlocks &predecessors) const;
    bool reachesAnyOf(const llvm::BasicBlock *bb, const std::set<const llvm::BasicBlock*> &blocks) const;
    bool isUser() const {return is_user; }
    bool isDiffAdded() const        {return diff_added; }
    bool isDiffRemoved() const      {return diff_removed; }
    bool isDiffChanged() const      {return diff_body || diff_sig; }
    bool isDiffChangedBody() const  {return diff_body; }
    bool isDiffChangedSig() const   {return diff_sig; }
    std::string getName() const { std::string result; if (function != nullptr) result = function->getName().str(); return result; }
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

    KFunction *getKFunction(llvm::Function *fn)
      { auto itr = functionMap.find(fn); if (itr != functionMap.end()) return itr->second; return nullptr; }

    KFunction *getKFunction(const std::string &name)
      { if (auto *fn = module->getFunction(name)) if (auto *kf = getKFunction(fn)) return kf; return nullptr; }

    // Functions which escape (may be called indirectly)
    // XXX change to KFunction
    std::set<llvm::Function*> escapingFunctions;

    InstructionInfoTable *infos;

    std::vector<llvm::Constant*> constants;
    std::map<llvm::Constant*, KConstant*> constantMap;
    KConstant* getKConstant(llvm::Constant *c);

    Cell *constantTable;

    // Mark function as part of the KLEE runtime
    void addInternalFunction(const llvm::Function *fn) { internalFunctions.insert(fn); }
    bool isInternalFunction(const llvm::Function *fn) const
      { return (fn != nullptr) && (internalFunctions.find(fn) != internalFunctions.end()); }

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
    llvm::LLVMContext *getContextPtr() const
      { llvm::LLVMContext *result = nullptr; if (module) result = &module->getContext(); return result; }
    llvm::Function *getFunction(const std::string &fn) const
      { llvm::Function *result = nullptr; if (module) result = module->getFunction(fn); return result; }

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

    bool isUserFunction(const llvm::Function* fn) const {
      return user_fns.find(fn) != user_fns.end();
    }

    void getUserFunctions(std::set<const llvm::Function*> &fns) const {
      fns.clear();
      for (auto itr = user_fns.begin(), end = user_fns.end(); itr != end; ++itr) fns.insert(*itr);
    }

    void getUserFunctions(std::set<std::string> &fns) const {
      fns.clear();
      for (auto itr = user_fns.begin(), end = user_fns.end(); itr != end; ++itr) fns.insert((*itr)->getName());
    }

    bool isUserGlobal(const llvm::GlobalVariable* gb) const {
      return user_gbs.find(gb) != user_gbs.end();
    }

    void getUserGlobals(std::set<const llvm::GlobalVariable*> &gbs) const {
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

    llvm::GlobalVariable *getGlobalVariable(const std::string &name) const
      { auto itr = mapGlobalVars.find(name); if (itr != mapGlobalVars.end()) return itr->second; return nullptr; }

    TraceType getModuleTraceType() const { return module_trace; }

    bool addDiffFnAdded(const std::string &name)
      { if (auto *kf = getKFunction(name)) { kf->diff_added = true; return true; } return false; }
    bool addDiffFnRemoved(const std::string &name)
      { if (auto *kf = getKFunction(name)) { kf->diff_removed = true; return true; } return false; }
    bool addDiffFnChangedBody(const std::string &name)
      { if (auto *kf = getKFunction(name)) { kf->diff_body = true; return true; } return false; }
    bool addDiffFnChangedSig(const std::string &name)
      { if (auto *kf = getKFunction(name)) { kf->diff_sig = true; return true; } return false; }
    bool addDiffGlobalAdded(const std::string &name)
      { if (auto *gv = getGlobalVariable(name)) { diff_gbs_added.insert(gv); return true; } return false; }
    bool addDiffGlobalRemoved(const std::string &name)
      { if (auto *gv = getGlobalVariable(name)) { diff_gbs_removed.insert(gv); return true; } return false; }
    bool addDiffGlobalChanged(const std::string &name)
      { if (auto *gv = getGlobalVariable(name)) { diff_gbs_changed.insert(gv); return true; } return false; }

  private:
    std::map<const llvm::Function*,unsigned> mapFnMarkers;
    std::map<const llvm::BasicBlock*,unsigned> mapBBMarkers;
    std::map<const llvm::FunctionType*,std::set<const llvm::Function*> >mapFnTypes;
    std::map<std::string,llvm::Type*> mapTypeDescs;
    std::set<const llvm::Function*> user_fns;
    std::set<const llvm::GlobalVariable*> user_gbs;
    std::map<std::string,llvm::GlobalVariable*> mapGlobalVars;
    TraceType module_trace;

    std::set<llvm::GlobalVariable*> diff_gbs_added;
    std::set<llvm::GlobalVariable*> diff_gbs_removed;
    std::set<llvm::GlobalVariable*> diff_gbs_changed;

  public:
    std::string pre_module;
    std::string post_module;
};

} // End klee namespace

#endif
