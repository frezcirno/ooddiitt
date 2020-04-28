//
// Created by rrutledge on 10/23/19.
//

#ifndef BRT_KLEE_STATECOMPARISON_H
#define BRT_KLEE_STATECOMPARISON_H

#include <string>
#include <deque>
#include <vector>
#include <map>
#include "klee/ExecutionState.h"

namespace llvm {
class GlobalVariable;
class Type;
}

namespace klee {

struct StateVersion {
  KModule *kmodule;
  std::map<const llvm::GlobalVariable*, MemoryObject*> global_map;
  ExecutionState *initialState;
  ExecutionState *finalState;
  TerminateReason term_reason;
  bool forked;
  std::deque<std::pair<KFunction*, ExecutionState*> > fn_returns;

  explicit StateVersion(KModule *k) :
      kmodule(k), initialState(nullptr), finalState(nullptr), term_reason(TerminateReason::Invalid), forked(false)  {}
  virtual ~StateVersion();
};

enum class DiffType {
  invalid,
  delta,
  info,
  warning,
  fail
};

struct CompareDiff {
  DiffType type;
  std::string element;
  std::string desc;

  explicit CompareDiff(DiffType t, const std::string &e = "", const std::string &d = "") : type(t), element(e), desc(d) {}
};

struct CompareCheckpoint {
  std::string fn;
  unsigned distance;
  std::deque<CompareDiff> diffs;

  explicit CompareCheckpoint(const std::string &f, unsigned d) : fn(f), distance(d) {}
};

std::string to_string(const CompareCheckpoint &checkpoint);
std::string to_string(const CompareDiff &diff);
std::string to_string(const std::set<unsigned> &nums);

class StateComparator {

  const TestCase &test;
  StateVersion &ver1;
  StateVersion &ver2;
  std::set<std::pair<uint64_t,uint64_t> > visited_ptrs;

  struct CompareGlobalEntry {
    std::string name;
    const MemoryObject *mo1;
    const MemoryObject *mo2;
    llvm::Type *type;
    CompareGlobalEntry(const std::string &n, const MemoryObject *m1, const MemoryObject *m2, llvm::Type *t)
        : name(n), mo1(m1), mo2(m2), type(t) {}
    bool operator<(const CompareGlobalEntry &that) const { return (this->name < that.name); }
  };
  std::set<CompareGlobalEntry> globals;
  const llvm::DataLayout *datalayout;
  Expr::Width ptr_width;
  std::set<KFunction*> blacklistedFns;
  std::set<llvm::Type*> blacklistedTypes;

public:
  StateComparator(const TestCase &t, StateVersion &v1, StateVersion &v2);
  void blacklistFunction(const std::string &name);
  void blacklistStructType(const std::string &name);
  bool diffs_found() const;

  const KInstruction *checkTermination();
  bool isEquivalent();
  bool reachedChanged() const
    { return ver1.finalState->reached_modified_fn || ver2.finalState == nullptr || ver2.finalState->reached_modified_fn; }

  std::deque<CompareCheckpoint> checkpoints;
  std::set<unsigned> oracle_ids;

private:

  bool compareExternalState();
  bool compareInternalState();
  bool alignFnReturns();
  void calcLongestCommonSubSeq(const std::vector<KFunction*> &seq1, const std::vector<KFunction*> &seq2, std::vector<KFunction*> &lcs);
  void dropFnReturns(std::deque<std::pair<KFunction*, ExecutionState*> > &rets, const std::vector<KFunction*> &kfs);

  void compareInternalState(KFunction *kf1, ExecutionState *state1, KFunction *kf2, ExecutionState *state2, bool is_final);
  void compareObjectStates(const ObjectState *os1, uint64_t offset1, KFunction *kf1, ExecutionState *state1,
                           const ObjectState *os2, uint64_t offset2, KFunction *kf2, ExecutionState *state2,
                           const std::string &name, llvm::Type *type);


  void compareMemoryObjects(const MemoryObject *mo1, uint64_t offset1, KFunction *kf1, ExecutionState *state1,
                            const MemoryObject *mo2, uint64_t offset2, KFunction *kf2, ExecutionState *state2,
                            const std::string &name, llvm::Type *type);

  void compareMemoryObjects(const MemoryObject *mo1, KFunction *kf1, ExecutionState *state1,
                            const MemoryObject *mo2, KFunction *kf2, ExecutionState *state2,
                            const std::string &name, llvm::Type *type)
    { compareMemoryObjects(mo1, 0, kf1, state1, mo2, 0, kf2, state2, name, type); }


  void compareRetExprs(const ref<klee::ConstantExpr> &expr1, KFunction *kf1, ExecutionState *state1,
                       const ref<klee::ConstantExpr> &expr2, KFunction *kf2, ExecutionState *state2,
                       llvm::Type *type);

  void comparePtrs(const ref<klee::ConstantExpr> &expr1, KFunction *kf1, ExecutionState *state1,
                   const ref<klee::ConstantExpr> &expr2, KFunction *kf2, ExecutionState *state2,
                   const std::string &name, llvm::PointerType *type);

  void comparePtrs(uint64_t addr1, KFunction *kf1, ExecutionState *state1,
                   uint64_t addr2, KFunction *kf2, ExecutionState *state2,
                   const std::string &name, llvm::PointerType *type);

  bool isBlacklisted(KFunction *fk) { return blacklistedFns.find(fk) != blacklistedFns.end(); }
  bool isBlacklisted(llvm::Type *type) { return blacklistedTypes.find(type) != blacklistedTypes.end(); }

};

}

#endif //BRT_KLEE_STATECOMPARISON_H
