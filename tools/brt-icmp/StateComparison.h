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

  explicit StateVersion(KModule *k) : kmodule(k), initialState(nullptr), finalState(nullptr), forked(false)  {}
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
  std::string fn;
  std::string element;
  unsigned distance;
  std::string desc;

  explicit CompareDiff(DiffType t) : type(t), distance(0) {}
};

struct CompareExtDiff : CompareDiff {
  explicit CompareExtDiff(const std::string &e) : CompareDiff(DiffType::delta) { fn = "@top"; element = e; distance = UINT_MAX; }
  CompareExtDiff(const std::string &e, const std::string &d) : CompareExtDiff(e) { desc = d; }
};

struct CompareIntDiff : CompareDiff {
  CompareIntDiff(KFunction *kf, const std::string &e, ExecutionState *state) : CompareDiff(DiffType::delta)
    { fn = kf->getName(); element = e; distance = state->distance; }
  CompareIntDiff(KFunction *kf, const std::string &e, ExecutionState *state, const std::string &d)
    : CompareIntDiff(kf, e, state) { desc = d; }
};

std::string to_string(const CompareDiff &diff);

class StateComparator {

  const TestCase &test;
  StateVersion &ver1;
  StateVersion &ver2;
  std::deque<CompareDiff> diffs;
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
  unsigned size_diffs() const {
    unsigned count = 0;
    for (const auto &diff : diffs) {
      if (diff.type == DiffType::delta) count += 1;
    }
    return count;
  }

  bool checkTermination();
  bool isEquivalent();
  bool beseechOracle() const { return ver2.finalState->o_asserts.empty(); }
  bool reachedChanged() const { return ver1.finalState->reached_modified_fn || ver2.finalState->reached_modified_fn; }

  bool empty() const { return diffs.empty(); }
  std::deque<CompareDiff>::iterator begin() { return diffs.begin(); }
  std::deque<CompareDiff>::iterator end() { return diffs.end(); }
  std::deque<CompareDiff>::const_iterator begin() const { return diffs.begin(); }
  std::deque<CompareDiff>::const_iterator end() const { return diffs.end(); }

private:

  bool compareExternalState();
  bool compareInternalState();
  bool alignFnReturns();
  bool compareInternalState(KFunction *kf1, ExecutionState *state1, KFunction *kf2, ExecutionState *state2);
  bool compareObjectStates(const ObjectState *os1, uint64_t offset1, KFunction *kf1, ExecutionState *state1,
                           const ObjectState *os2, uint64_t offset2, KFunction *kf2, ExecutionState *state2,
                           const std::string &name, llvm::Type *type);


  bool compareMemoryObjects(const MemoryObject *mo1, uint64_t offset1, KFunction *kf1, ExecutionState *state1,
                            const MemoryObject *mo2, uint64_t offset2, KFunction *kf2, ExecutionState *state2,
                            const std::string &name, llvm::Type *type);

  bool compareMemoryObjects(const MemoryObject *mo1, KFunction *kf1, ExecutionState *state1,
                            const MemoryObject *mo2, KFunction *kf2, ExecutionState *state2,
                            const std::string &name, llvm::Type *type)
    { return compareMemoryObjects(mo1, 0, kf1, state1, mo2, 0, kf2, state2, name, type); }


  bool compareRetExprs(const ref<klee::ConstantExpr> &expr1, KFunction *kf1, ExecutionState *state1,
                       const ref<klee::ConstantExpr> &expr2, KFunction *kf2, ExecutionState *state2,
                       llvm::Type *type);

  bool comparePtrs(const ref<klee::ConstantExpr> &expr1, KFunction *kf1, ExecutionState *state1,
                   const ref<klee::ConstantExpr> &expr2, KFunction *kf2, ExecutionState *state2,
                   const std::string &name, llvm::PointerType *type);

  bool comparePtrs(uint64_t addr1, KFunction *kf1, ExecutionState *state1,
                   uint64_t addr2, KFunction *kf2, ExecutionState *state2,
                   const std::string &name, llvm::PointerType *type);

  bool isBlacklisted(KFunction *fk) { return blacklistedFns.find(fk) != blacklistedFns.end(); }
  bool isBlacklisted(llvm::Type *type) { return blacklistedTypes.find(type) != blacklistedTypes.end(); }


  static void emitRetSequence(std::ostringstream &ss, std::deque<std::pair<KFunction*, ExecutionState*> > &fn_returns);
};

}

#endif //BRT_KLEE_STATECOMPARISON_H
