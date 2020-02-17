//
// Created by rrutledge on 10/23/19.
//

#ifndef BRT_KLEE_STATECOMPARISON_H
#define BRT_KLEE_STATECOMPARISON_H

#include <deque>
#include <string>

namespace klee {

class KModule;
class ExecutionState;

struct CompareState {
  KModule *kmodule;
  ExecutionState *initialState;
  ExecutionState *finalState;
  bool forked;
  std::deque<std::string> fn_returns;

  explicit CompareState(KModule *k) : kmodule(k), initialState(nullptr), finalState(nullptr), forked(false) {}
  ~CompareState() { delete initialState; delete finalState; }
};

}

bool CompareExternalExecutions(klee::CompareState &version1, klee::CompareState &version2, std::deque<std::string> &diffs);
bool CompareInternalExecutions(klee::CompareState &version1, klee::CompareState &version2, std::deque<std::string> &diffs);


#endif //BRT_KLEE_STATECOMPARISON_H
