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
  std::map<const llvm::GlobalVariable *, MemoryObject *> global_map;
  ExecutionState *initialState;
  ExecutionState *finalState;
  bool forked;
  std::deque<std::pair<KFunction *, ExecutionState *> > fn_returns;

  explicit StateVersion(KModule *k) : kmodule(k), initialState(nullptr), finalState(nullptr), forked(false)  {}
  virtual ~StateVersion();
};

struct CompareDiff {
  std::string desc;

  explicit CompareDiff(const std::string &d) : desc(d) { }
};

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
  };
  std::vector<CompareGlobalEntry> globals;
  const llvm::DataLayout *datalayout;
  Expr::Width ptr_width;

public:
  StateComparator(const TestCase &t, StateVersion &v1, StateVersion &v2);

  bool alignFnReturns();
  void doCompare();

  bool empty() const { return diffs.empty(); }
  std::deque<CompareDiff>::iterator begin() { return diffs.begin(); }
  std::deque<CompareDiff>::iterator end() { return diffs.end(); }
  std::deque<CompareDiff>::const_iterator begin() const { return diffs.begin(); }
  std::deque<CompareDiff>::const_iterator end() const { return diffs.end(); }

private:

  void compareExternalState();
  void compareInternalState();
  void compareInternalState(KFunction *kf1, ExecutionState *state1, KFunction *kf2, ExecutionState *state2);
  void compareObjectStates(const ObjectState *os1, uint64_t offset1, ExecutionState *state1,
                           const ObjectState *os2, uint64_t offset2, ExecutionState *state2,
                           const std::string &name, llvm::Type *type);


  void compareMemoryObjects(const MemoryObject *mo1, uint64_t offset1, ExecutionState *state1,
                            const MemoryObject *mo2, uint64_t offset2, ExecutionState *state2,
                            const std::string &name, llvm::Type *type);

  void compareMemoryObjects(const MemoryObject *mo1, ExecutionState *state1,
                            const MemoryObject *mo2, ExecutionState *state2,
                            const std::string &name, llvm::Type *type)
    { compareMemoryObjects(mo1, 0, state1, mo2, 0, state2, name, type); }


  void compareRetExprs(const ref<klee::ConstantExpr> &expr1, ExecutionState *state1,
                       const ref<klee::ConstantExpr> &expr2, ExecutionState *state2,
                       const std::string &name, llvm::Type *type);

  void comparePtrs(const ref<klee::ConstantExpr> &addr1, ExecutionState *state1,
                   const ref<klee::ConstantExpr> &addr2, ExecutionState *state2,
                   const std::string &name, llvm::PointerType *type);


};

}

#endif //BRT_KLEE_STATECOMPARISON_H
