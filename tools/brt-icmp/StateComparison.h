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

struct CompareDiff {
  std::string desc;

  explicit CompareDiff(const std::string &d) : desc(d) { }
};

struct CompareState {
  KModule *kmodule;
  std::map<const llvm::GlobalVariable*,MemoryObject*> global_map;
  ExecutionState *initialState;
  ExecutionState *finalState;
  bool forked;
  std::deque<std::pair<KFunction*,ExecutionState*> > fn_returns;

  explicit CompareState(KModule *k) : kmodule(k), initialState(nullptr), finalState(nullptr), forked(false) {}
  virtual ~CompareState();

  bool alignFnReturns(CompareState &that);
  bool compareExternalState(const TestCase &test, const CompareState &that, std::deque<CompareDiff> &diffs) const;
  bool compareInternalState(const TestCase &test, const CompareState &that, std::deque<CompareDiff> &diffs) const;

private:

  struct CompareGlobalEntry {
    const MemoryObject *mo1;
    const MemoryObject *mo2;
    const llvm::Type *type;
    CompareGlobalEntry(const MemoryObject *m1, const MemoryObject *m2, const llvm::Type *t)
      : mo1(m1), mo2(m2), type(t) {}
  };

  static void compareInternalState(KFunction *kf1, ExecutionState *state1,
                                   KFunction *kf2, ExecutionState *state2,
                                   const std::vector<CompareGlobalEntry> &globals,
                                   std::deque<CompareDiff> &diffs);

  static void compareMemoryObjects(const MemoryObject *mo1, ExecutionState *state1,
                                   const MemoryObject *mo2, ExecutionState *state2,
                                   const llvm::Type *type,
                                   std::deque<CompareDiff> &diffs);

  static void compareExprs(const ref<klee::ConstantExpr> &expr1, ExecutionState *state1,
                           const ref<klee::ConstantExpr> &expr2, ExecutionState *state2,
                           const llvm::Type *type,
                           std::deque<CompareDiff> &diffs);

};

}

//bool CompareExternalExecutions(klee::CompareState &version1, klee::CompareState &version2, std::deque<std::string> &diffs);
//bool CompareInternalExecutions(klee::CompareState &version1, klee::CompareState &version2, std::deque<std::string> &diffs);


#endif //BRT_KLEE_STATECOMPARISON_H
