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
#include "ModuleTypes.h"

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
  struct InstructionInfo;
  class KModule;
  template<class T> class ref;

  typedef std::pair<const llvm::BasicBlock*,const llvm::BasicBlock*> CFGEdge;
  typedef std::set_ex<const llvm::BasicBlock*> BasicBlocks;
  typedef llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop> KLoop;

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
    std::string fn_name;

    // loop analysis
    llvm::DominatorTree domTree;
    KLoop kloop;
    std::set_ex<const llvm::Loop*> loops;

    std::string src_location;

    bool is_user;
    unsigned fnID;
    bool diff_added;
    bool diff_removed;
    bool diff_body;
    bool diff_sig;

    // hashed values
    uint64_t fn_hash;
    std::map<const llvm::BasicBlock *, uint64_t> bb_hashes;

    uint64_t getHashValue();
    void calcFnHash();
    uint64_t calcBBHash(const llvm::BasicBlock *bb);
    uint64_t getHashValue(const llvm::BasicBlock *bb) const {
      auto itr = bb_hashes.find(bb);
      if (itr != bb_hashes.end())
        return itr->second;
      else
        return 0;
    }


    explicit KFunction(llvm::Function*, bool user_fn, KModule *);
    ~KFunction();

    static unsigned getArgRegister(unsigned index) { return index; }
    bool isLoopHeader(const llvm::BasicBlock *bb) const
      { const auto *loop = kloop.getLoopFor(bb); return (loop && loop->getHeader() == bb); }
    void getSuccessorBBs(const llvm::BasicBlock *bb, BasicBlocks &successors) const;
    void getPredecessorBBs(const llvm::BasicBlock *bb, BasicBlocks &predecessors) const;
    bool reachesAnyOf(const llvm::BasicBlock *bb, const std::set_ex<const llvm::BasicBlock*> &blocks) const;
    bool isUser() const {return is_user; }
    bool isDiffAdded() const        {return diff_added; }
    bool isDiffRemoved() const      {return diff_removed; }
    bool isDiffChanged() const      {return diff_body || diff_sig; }
    bool isDiffChangedBody() const  {return diff_body; }
    bool isDiffChangedSig() const   {return diff_sig; }
    const std::string &getName() const { return fn_name; }
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
    llvm::DataLayout *targetData;

    // Some useful functions to know the address of
    llvm::Function *kleeMergeFn;

    // Our shadow versions of LLVM structures.
    std::vector<KFunction*> functions;
    std::map<llvm::Function*, KFunction*> functionMap;
    ModuleTypes module_types;

    KFunction *getKFunction(llvm::Function *fn) const
      { auto itr = functionMap.find(fn); if (itr != functionMap.end()) return itr->second; return nullptr; }

    KFunction *getKFunction(const std::string &name) const
      { if (auto *fn = module->getFunction(name)) if (auto *kf = getKFunction(fn)) return kf; return nullptr; }

    // Functions which escape (may be called indirectly)
    // XXX change to KFunction
    std::set_ex<llvm::Function *> escapingFunctions;
    std::set_ex<const llvm::Function *> externalFunctions;

    InstructionInfoTable *infos;

    std::vector<llvm::Constant*> constants;
    std::map<llvm::Constant*, KConstant*> constantMap;
    KConstant* getKConstant(llvm::Constant *c);

    Cell *constantTable;

    // Mark function as part of the KLEE runtime
    void addInternalFunction(const llvm::Function *fn) { internalFunctions.insert(fn); }
    bool isInternalFunction(const llvm::Function *fn) const
    { return (fn != nullptr) && (internalFunctions.contains(fn)); }
    bool isDefinedFunction(llvm::Function *fn) { return getKFunction(fn) != nullptr; }

    llvm::Function *getTargetFunction(llvm::Value *value) const;

  private:

    // Functions which are part of KLEE runtime
    std::set_ex<const llvm::Function*> internalFunctions;
    std::map<llvm::Function*,std::set_ex<unsigned>> fn_const_params;

  public:
    explicit KModule(llvm::Module *_module);
    ~KModule();

    llvm::Module *detachModule() { llvm::Module *m = module; module = nullptr; return m; }
    bool isPrepared() const { return module != nullptr && klee::isPrepared(module); }
    std::string getModuleIdentifier() const
      { std::string result; if (module) result = module->getModuleIdentifier(); return result; }
    llvm::LLVMContext *getContextPtr() const
      { llvm::LLVMContext *result = nullptr; if (module) result = &module->getContext(); return result; }
    llvm::Function *getFunction(const std::string &fn) const
      { llvm::Function *result = nullptr; if (module) result = module->getFunction(fn); return result; }

    bool isConstFnArg(llvm::Function *fn, unsigned idx) const {
      auto itr = fn_const_params.find(fn);
      if (itr != fn_const_params.end()) {
        return itr->second.contains(idx);
      }
      return false;
    }

    bool isConstFnArg(const std::string &fn_name, unsigned idx) const {
      if (llvm::Function *fn = module->getFunction(fn_name)) {
        return isConstFnArg(fn, idx);
      }
      return false;
    }

    /// Initialize local data structures.
    //
    void prepare();
    void transform(const Interpreter::ModuleOptions &opts);
    bool hasOracle() const { return getKFunction("__o_assert_fail") != nullptr; }
    void insertSetlocaleIntoLibcInit(const std::string &name);

    /// Return an id for the given constant, creating a new one if necessary.
    unsigned getConstantID(llvm::Constant *c, KInstruction* ki);

    unsigned getFnID(const llvm::Function *fn) const;
    unsigned getBBlockID(const llvm::BasicBlock *bb) const;
    std::pair<unsigned,unsigned> getMarker(const llvm::Function *fn, const llvm::BasicBlock *bb);
    void getMarkedFns(std::set_ex<const llvm::Function*> &fns) {
      fns.clear();
      for (auto itr = mapFnMarkers.begin(), end = mapFnMarkers.end(); itr != end; ++itr) fns.insert(itr->first);
    }

    void getUserFnsOfType(const llvm::FunctionType *ft, std::vector<const llvm::Function *> &fns) const {
      const auto &fnd = mapFnTypes.find(ft);
      if (fnd != mapFnTypes.end()) {
        auto &matching = fnd->second;
        fns.reserve(matching.size());
        for (auto fn : matching) {
          if (user_fns.contains(fn)) fns.push_back(fn);
        }
      }
    }

    void getUserFunctions(std::set_ex<const llvm::Function*> &fns) const {
      fns.clear();
      for (auto itr = user_fns.begin(), end = user_fns.end(); itr != end; ++itr) fns.insert(*itr);
    }

    void getUserFunctions(std::set_ex<std::string> &fns) const {
      fns.clear();
      for (auto itr = user_fns.begin(), end = user_fns.end(); itr != end; ++itr) fns.insert((*itr)->getName());
    }

    void getUserSources(std::set_ex<std::string> &srcs) const;

    bool isPossibleLibrarySource(const std::string &pname, const std::string &fname, const std::string &vname) const {

      UNUSED(vname);
      if (boost::starts_with(pname, "libc/") || boost::starts_with(pname, "./include")) return true;
      if (fname == "locale_data.c") return true;
      return false;
    }

    void getExternalFunctions(std::set_ex<const llvm::Function*> &fns) const {
      fns.clear();
      for (auto itr = externalFunctions.begin(), end = externalFunctions.end(); itr != end; ++itr) fns.insert(*itr);
    }

    void getExternalFunctions(std::set_ex<std::string> &fns) const {
      fns.clear();
      for (auto itr = externalFunctions.begin(), end = externalFunctions.end(); itr != end; ++itr) fns.insert((*itr)->getName());
    }

    bool isUserGlobal(const llvm::GlobalVariable* gb) const {
      return user_gbs.contains(gb);
    }

    void getUserGlobals(std::set_ex<const llvm::GlobalVariable*> &gbs) const {
      gbs.clear();
      for (auto itr = user_gbs.begin(), end = user_gbs.end(); itr != end; ++itr) gbs.insert(*itr);
    }

    void getUserGlobals(std::set_ex<std::string> &gbs) {
      gbs.clear();
      for (auto itr = user_gbs.begin(), end = user_gbs.end(); itr != end; ++itr) {
        const llvm::GlobalVariable *gv = *itr;
        gbs.insert(gv->getName());
      }
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
    bool addDiffGlobalChanged(const std::string &name) {
      if (auto *gv = getGlobalVariable(name)) { diff_gbs_changed.insert(gv); return true; } return false; }

    bool isDiffGlobalAdded(const std::string &name) const
      { if (auto *gv = getGlobalVariable(name)) { return isDiffGlobalAdded(gv); } return false; }
    bool isDiffGlobalAdded(llvm::GlobalVariable *gv) const { return diff_gbs_added.contains(gv); }

    bool isDiffGlobalRemoved(const std::string &name) const
      { if (auto *gv = getGlobalVariable(name)) { return isDiffGlobalRemoved(gv); } return false; }
    bool isDiffGlobalRemoved(llvm::GlobalVariable *gv) const { return diff_gbs_removed.contains(gv); }

    bool isDiffGlobalChanged(const std::string &name) const
      { if (auto *gv = getGlobalVariable(name)) { return isDiffGlobalChanged(gv); } return false; }
    bool isDiffGlobalChanged(llvm::GlobalVariable *gv) const { return diff_gbs_changed.contains(gv); }

    bool isDiffGlobalModified(const std::string &name) const
      { if (auto *gv = getGlobalVariable(name)) { return isDiffGlobalModified(gv); } return false; }
    bool isDiffGlobalModified(const llvm::GlobalVariable *gv) const
      { auto *v = const_cast<llvm::GlobalVariable*>(gv); return isDiffGlobalAdded(v) || isDiffGlobalRemoved(v) || isDiffGlobalChanged(v); }

    void addTargetedBBlocks(const KFunction *kf, const std::set_ex<unsigned> &bblocks);
    void addTargetedBBlocks(const std::string &fn_name, const std::set_ex<unsigned> &bblocks) {
      if (KFunction *kf = getKFunction(fn_name)) addTargetedBBlocks(kf, bblocks);
    }
    // to target an entire function, add each of its blocks
    void addTargetedBBlocks(const KFunction *kf) {
      for (llvm::BasicBlock &bb : *(kf->function)) {
        targeted_bblocks.insert(&bb);
      }
    }

    void addTargetedBBlocks(const std::string &fn_name) {
      if (KFunction *kf = getKFunction(fn_name)) addTargetedBBlocks(kf);
    }

    void getTargetedFns(std::set_ex<KFunction *> &kfns) const;
    void getTargetedFns(std::set_ex<std::string> &names) const {
      std::set_ex<KFunction *> kfns;
      getTargetedFns(kfns);
      for (auto *kf : kfns) {
        names.insert(kf->getName());
      }
    }

    bool isTargetedFn(const std::string &name) const {
      if (llvm::Function *fn = getFunction(name)) {
        return isTargetedFn(fn);
      }
      return false;
    }
    bool isTargetedFn(KFunction *kf) const { return isTargetedFn(kf->function); }
    bool isTargetedFn(llvm::Function *fn) const {
      for (llvm::BasicBlock &bb : *fn) {
        if (targeted_bblocks.contains(&bb)) return true;
      }
      return false;
    }

    bool isTargetedBBlock(llvm::BasicBlock *bb) const { return targeted_bblocks.contains(bb); }

    bool isPrevModule() const { return is_prev_module; }
    bool isPostModule() const { return !is_prev_module; }

  private:
    bool replaceFunction(llvm::Function *old_fn, llvm::Function *new_fn);
    void removeKnownFnDuplicates();
    bool removeFnDuplicates(llvm::Function *fn);
    llvm::Function *getOrPromoteFnDuplicate(const std::string &name);

  private:
    std::map<const llvm::Function*,unsigned> mapFnMarkers;
    std::map<const llvm::BasicBlock*,unsigned> mapBBMarkers;
    std::map<const llvm::FunctionType*,std::set_ex<const llvm::Function*> >mapFnTypes;
    std::map<std::string,llvm::Type*> mapTypeDescs;
    std::set_ex<const llvm::Function*> user_fns;
    std::set_ex<const llvm::GlobalVariable*> user_gbs;
    std::map<std::string,llvm::GlobalVariable*> mapGlobalVars;
    TraceType module_trace;

    std::set_ex<llvm::GlobalVariable*> diff_gbs_added;
    std::set_ex<llvm::GlobalVariable*> diff_gbs_removed;
    std::set_ex<llvm::GlobalVariable*> diff_gbs_changed;
    std::set_ex<llvm::BasicBlock *> targeted_bblocks;

  public:
    std::string prev_module;
    std::string post_module;
    bool is_prev_module;
};

} // End klee namespace

#endif
