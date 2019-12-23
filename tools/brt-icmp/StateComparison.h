//
// Created by rrutledge on 10/23/19.
//

#ifndef BRT_KLEE_STATECOMPARISON_H
#define BRT_KLEE_STATECOMPARISON_H

namespace klee {

class KModule;
class ExecutionState;

struct CompareState {
  KModule *kmodule;
  ExecutionState *state;
};

}

bool CompareExecutions(klee::CompareState &version1, klee::CompareState &version2);


#endif //BRT_KLEE_STATECOMPARISON_H
