//
// Created by rrutledge on 10/23/19.
//

#include "StateComparison.h"
#include <vector>
#include <boost/filesystem.hpp>

#include "klee/ExecutionState.h"
#include "klee/Internal/System/Memory.h"

#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace std;

namespace klee {

string to_string(const vector<unsigned char> &buffer) {
  ostringstream bytes;
  for (auto itr = buffer.begin(), end = buffer.end(); itr != end; ++itr) {
    unsigned char hi = (unsigned char) (*itr >> 4);
    unsigned char low = (unsigned char) (*itr & 0x0F);
    hi = (unsigned char) ((hi > 9) ? ('A' + (hi - 10)) : ('0' + hi));
    low = (unsigned char) ((low > 9) ? ('A' + (low - 10)) : ('0' + low));
    bytes << hi << low;
  }
  return bytes.str();
}

string to_string(const CharacterOutput &out) {

  vector<unsigned char> buffer;
  out.get_data(buffer);
  return to_string(buffer);
}

CompareState::~CompareState() {

  // modules are deleted explicitly
  delete initialState;
  delete finalState;
  for (auto &pr : fn_returns) {
    delete pr.second;
  }
}

bool CompareState::alignFnReturns(CompareState &that) {

  if (fn_returns.size() == that.fn_returns.size()) {

    // RLR TODO: if this test fails, try to align the function calls
    //  (by inserting null states or skipping states (minimum edit distance?)
    auto itrThis = fn_returns.begin(), endThis = fn_returns.end();
    auto itrThat = that.fn_returns.begin(), endThat = that.fn_returns.end();
    while (itrThis != endThis) {
      if (itrThis->first->getName() != itrThat->first->getName()) return false;
      itrThis++; itrThat++;
    }
    return true;
  }
  return false;
}

bool CompareState::compareExternalState(const TestCase &test, const CompareState &that, std::deque<CompareDiff> &diffs) const {

  unsigned num_original_diffs = diffs.size();

  // each  must have zero or one final argument, it must be an int, and they must be equal
  unsigned num_return_vals1 = finalState->arguments.size();
  unsigned num_return_vals2 = that.finalState->arguments.size();

  if (num_return_vals1 > 1 || num_return_vals2 > 1) {
    // ensure both final states have a correct number of return values
    diffs.emplace_back("too many return values");
  } else if (num_return_vals1 != num_return_vals2) {
    // ensure both final states have the same number of return values
    diffs.emplace_back("mismatched return values");
  } else if (num_return_vals1 == 1) {
    // if they have one value, make sure its the same (could be no value in the case of an abort)
    unsigned exit_code1 = cast<klee::ConstantExpr>(finalState->arguments[0])->getZExtValue(Expr::Int32);
    unsigned exit_code2 = cast<klee::ConstantExpr>(that.finalState->arguments[0])->getZExtValue(Expr::Int32);
    if (exit_code1 != exit_code2) {
      diffs.emplace_back("different return value");
    }
  }

  string stdout1 = to_string(finalState->stdout_capture);
  string stdout2 = to_string(that.finalState->stdout_capture);
  if (stdout1 != stdout2) {
    diffs.emplace_back("different stdout");
  }

  string stderr1 = to_string(finalState->stderr_capture);
  string stderr2 = to_string(that.finalState->stderr_capture);
  if (stderr1 != stderr2) {
    diffs.emplace_back("different stderr");
  }

  return diffs.size() == num_original_diffs;
}

bool CompareState::compareInternalState(const TestCase &test, const CompareState &that, std::deque<CompareDiff> &diffs) const {

  unsigned num_original_diffs = diffs.size();
  if (fn_returns.size() != that.fn_returns.size()) {
    diffs.emplace_back("mismatched count of return states");
  } else {

    // get the set of global variables to compare.  These are only
    // user globals (i.e. not stdlib) in both modules and of equivalent types
    vector<CompareGlobalEntry> globals;
    set<const GlobalVariable*> gbs1;
    kmodule->getUserGlobals(gbs1);
    globals.reserve(gbs1.size());
    for (const GlobalVariable *gv1 : gbs1) {
      assert(gv1 != nullptr);
      const auto &itr1 = global_map.find(gv1);
      if (itr1 != global_map.end()) {
        const GlobalVariable *gv2 = that.kmodule->getGlobalVariable(gv1->getName());
        if (gv2 != nullptr) {
          Type *type = gv1->getType();
          if (isEquivalentType(type, gv2->getType())) {
            const auto &itr2 = that.global_map.find(gv2);
            if (itr2 != that.global_map.end()) {
              globals.emplace_back(itr1->second, itr2->second, type);
            }
          }
        }
      }
    }

    // check each of the intermediate states
    auto itrThis = fn_returns.begin(), endThis = fn_returns.end();
    auto itrThat = that.fn_returns.begin(), endThat = that.fn_returns.end();
    while (itrThis != endThis) {

      if (itrThis->first->getName() != itrThat->first->getName()) {
        diffs.emplace_back("function name mismatch in return trace");
      } else {
        compareInternalState(itrThis->first, itrThis->second, itrThat->first, itrThat->second, globals, diffs);
      }

      ++itrThis; ++itrThat;
    }

    // check the final state
    KFunction *kf1 = kmodule->getKFunction(test.entry_fn);
    KFunction *kf2 = that.kmodule->getKFunction(test.entry_fn);
    compareInternalState(kf1, finalState, kf2, that.finalState, globals, diffs);
  }

  return diffs.size() == num_original_diffs;
}


void CompareState::compareInternalState(KFunction *kf1, ExecutionState *state1,
                                        KFunction *kf2, ExecutionState *state2,
                                        const std::vector<CompareGlobalEntry> &globals,
                                        std::deque<CompareDiff> &diffs) {

  Function *fn1 = kf1->function;
//  Module *mod1 = fn1->getParent();
  Function *fn2 = kf2->function;
//  Module *mod2 = fn2->getParent();

  // check the return value
  if (isEquivalentType(fn1->getReturnType(), fn2->getReturnType())) {
    Type *type = fn1->getReturnType();
    if (!type->isVoidTy()) {
      // RLR TODO: need a better way of getting the return values from intermediate functions

    }
  }

  // check output devices
  string stdout1 = to_string(state1->stdout_capture);
  string stdout2 = to_string(state2->stdout_capture);
  if (stdout1 != stdout2) {
    diffs.emplace_back("different stdout");
  }

  string stderr1 = to_string(state1->stderr_capture);
  string stderr2 = to_string(state2->stderr_capture);
  if (stderr1 != stderr2) {
    diffs.emplace_back("different stderr");
  }

  // finally, check user global variables
  for (const auto &entry : globals) {
    compareMemoryObjects(entry.mo1, state1, entry.mo2, state2, entry.type, diffs);
  }
}

void CompareState::compareMemoryObjects(const MemoryObject *mo1, ExecutionState *state1,
                                        const MemoryObject *mo2, ExecutionState *state2,
                                        const llvm::Type *type,
                                        std::deque<CompareDiff> &diffs) {


}



} // end klee namespace
