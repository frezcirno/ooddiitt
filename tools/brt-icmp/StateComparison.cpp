// Created by rrutledge on 10/23/19.
//

#include "StateComparison.h"
#include <vector>
#include <llvm/Support/CommandLine.h>

#include "llvm/IR/DataLayout.h"
#include "llvm/Support/raw_ostream.h"
#include "klee/Internal/System/Memory.h"
#include "klee/Internal/Module/Cell.h"

#include <boost/filesystem.hpp>
#include "dtl/dtl.hpp"

using namespace llvm;
using namespace std;
namespace fs=boost::filesystem;

namespace klee {

cl::opt<bool> ReturnsFitLCS("returns-fit-lcs", cl::init(true), cl::desc("align function return checkpoints along longest common subsequence"));

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

string to_data_string(const CharacterOutput &out) {

  vector<unsigned char> buffer;
  out.get_data(buffer);
  return to_string(buffer);
}

string to_char_string(const CharacterOutput &out) {

  string result;
  vector<unsigned char> buffer;
  out.get_data(buffer);
  result.reserve(buffer.size() * 2); // just a guess, due to escaped chars
  for (unsigned char &ch : buffer) {
    if (isprint(ch))  {
      if (ch == '\\') {
        result += "\\\\";
      } else {
        result += ch;
      }
    } else {
      unsigned char hi = (unsigned char) (ch >> 4);
      unsigned char low = (unsigned char) (ch & 0x0F);
      hi = (unsigned char) ((hi > 9) ? ('A' + (hi - 10)) : ('0' + hi));
      low = (unsigned char) ((low > 9) ? ('A' + (low - 10)) : ('0' + low));
      result += '\\';
      result += hi;
      result += low;
    }
  }
  return result;
}

std::string to_string(const CompareCheckpoint &checkpoint) {

  ostringstream ss;
  ss << checkpoint.fn << ';';
  if (checkpoint.min_distance != UINT32_MAX) ss << checkpoint.min_distance;
  else ss << '+';
  ss << ';';
  if (checkpoint.stack_distance != UINT32_MAX) ss << checkpoint.stack_distance;
  else ss << '+';
  ss << ';';
  if (checkpoint.linear_distance != UINT32_MAX) ss << checkpoint.linear_distance;
  else ss << '+';
  return ss.str();
}

std::string to_string(const set<unsigned> &nums) {

  ostringstream ss;
  for (auto itr = nums.begin(), end = nums.end(); itr != end; ++itr) {
    if (itr != nums.begin()) ss << ',';
    ss << *itr;
  }
  return ss.str();
}

std::string to_string(const CompareDiff &diff) {

  static const char type_designators[] = { 'I', 'D', 'I', 'W', 'F' };
  ostringstream ss;

  ss << type_designators[(unsigned) diff.type] << ';' << diff.element << ';' << diff.desc;
  return ss.str();
}

StateVersion::~StateVersion() {

  // modules are deleted implicitly
  delete initialState;
  delete finalState;

  for (auto &pr : fn_returns) {
    delete pr.second;
  }
}

StateComparator::StateComparator(const string &tn, const TestCase &t, StateVersion &v1, StateVersion &v2) :
  test(t), test_name(tn), ver1(v1), ver2(v2), datalayout(ver1.kmodule->targetData) {

  ptr_width = datalayout->getPointerSizeInBits();
  // get a list of oracle ids encountered during the rply execution
  if (v2.finalState != nullptr) {
    for (const auto &entry : v2.finalState->o_asserts) {
      oracle_ids.insert(entry.first);
    }
  }

  // never compare on return for some functions
  blacklistFunction("xrealloc");
  blacklistFunction("x2nrealloc");
  blacklistFunction("_brt_oracle");

  // and never compare some types (due to type-abuse by stdlib)
  blacklistStructType("_IO_FILE");
  blacklistStructType("__STDIO_FILE_STRUCT");
  blacklistStructType("__mbstate_t");
  blacklistStructType("__locale_mmap_t");
  blacklistStructType("__codeset_8_bit_t");
  blacklistStructType("ppfs_t");
  blacklistStructType("printf_info");
  blacklistStructType("scan_cookie");
}

void StateComparator::blacklistFunction(const string &name) {

  if (KFunction *kf = ver1.kmodule->getKFunction(name)) blacklistedFns.insert(kf);
  if (KFunction *kf = ver2.kmodule->getKFunction(name)) blacklistedFns.insert(kf);
}

void StateComparator::blacklistStructType(const string &name) {

  ver1.kmodule->module_types.addMatchingStructTypes(name, blacklistedTypes);
  ver2.kmodule->module_types.addMatchingStructTypes(name, blacklistedTypes);
}

const KInstruction *StateComparator::checkTermination() {

  const KInstruction *result = nullptr;
  if (!(is_valid(ver1.term_reason) && (ver1.term_reason != ver2.term_reason))) {
    if (ver2.finalState != nullptr) {
      result = ver2.finalState->instFaulting;
    }
  }
  return result;
}

bool StateComparator::alignFnReturns() {

  // main with constrained globals means we will only be compariing external state.
  // return alignment is not relevant
  if (test.is_main() && !test.unconstraintFlags.isUnconstrainGlobals()) {
    return true;
  }

  // if ver2 did not complete, we will also not be comparing internal state
  if (ver2.finalState == nullptr || ver2.finalState->status != StateStatus::Completed) {
    return true;
  }

  // discard the return states from blacklisted fns
  for (auto itr = ver1.fn_returns.begin(); itr != ver1.fn_returns.end(); ) {
    if (isBlacklisted(itr->first)) itr = ver1.fn_returns.erase(itr);
    else ++itr;
  }

  for (auto itr = ver2.fn_returns.begin(); itr != ver2.fn_returns.end(); ) {
    if (isBlacklisted(itr->first)) itr = ver2.fn_returns.erase(itr);
    else ++itr;
  }

  map<KFunction*,KFunction*> ver1_to_ver2;
  map<KFunction*,KFunction*> ver2_to_ver1;
  for (auto itr = ver1.fn_returns.begin(), end = ver1.fn_returns.end(); itr != end; ++itr) {
    KFunction *kf1 = itr->first;
    KFunction *kf2 = ver2.kmodule->getKFunction(kf1->getName());
    assert(kf2);
    ver1_to_ver2.insert(make_pair(kf1, kf2));
    ver2_to_ver1.insert(make_pair(kf2, kf1));
  }

  if (ver1.fn_returns.size() == ver2.fn_returns.size()) {
    auto itr1 = ver1.fn_returns.begin(), end1 = ver1.fn_returns.end();
    auto itr2 = ver2.fn_returns.begin();
    while (itr1 != end1) {
      if (itr1->first != ver2_to_ver1[itr2->first]) {
        return false;
      }
      ++itr1; ++itr2;
    }
    return true;
  }

  if (ReturnsFitLCS) {

    vector<KFunction *> seq1, seq2, lcs;
    seq1.reserve(ver1.fn_returns.size());
    for (auto itr = ver1.fn_returns.begin(), end = ver1.fn_returns.end(); itr != end; ++itr) {
      seq1.push_back(itr->first);
    }
    seq2.reserve(ver2.fn_returns.size());
    for (auto itr = ver2.fn_returns.begin(), end = ver2.fn_returns.end(); itr != end; ++itr) {
      seq2.push_back(ver2_to_ver1[itr->first]);
    }

    calcLongestCommonSubSeq(seq1, seq2, lcs);

    if (!lcs.empty()) {
      dropFnReturns(ver1.fn_returns, lcs);
      for (unsigned idx = 0; idx < lcs.size(); ++idx) {
        lcs[idx] = ver1_to_ver2[lcs[idx]];
      }
      dropFnReturns(ver2.fn_returns, lcs);
      return true;
    }
  }
  return false;
}

void StateComparator::dropFnReturns(deque<pair<KFunction*, ExecutionState*> > &rets, const vector<KFunction*> &kfs) {

  assert(rets.size() >= kfs.size());

  // drop all fn_returns not in lcs sequence
  unsigned idx = 0;
  for (auto itr = rets.begin(); itr != rets.end(); ) {
    if (idx >= kfs.size() || itr->first != kfs[idx]) {
      itr = rets.erase(itr);
    } else {
      ++itr;
      ++idx;
    }
  }
  assert(rets.size() == kfs.size());
}

void StateComparator::calcLongestCommonSubSeq(const vector<KFunction*> &seq1,
                                              const vector<KFunction*> &seq2,
                                              vector<KFunction*> &lcs) {

  // calculate longest length
  unsigned len[seq1.size() + 1][seq2.size() + 1];

  for (unsigned idx1 = 0; idx1 <= seq1.size(); ++idx1) {
    for (unsigned idx2 = 0; idx2 <= seq2.size(); ++idx2) {
      unsigned new_length;
      if ((idx1 == 0) || (idx2 == 0)) {
        new_length = 0;
      } else if (seq1[idx1 - 1] == seq2[idx2 - 1]) {
        new_length = len[idx1 - 1][idx2 - 1] + 1;
      } else {
        new_length = max(len[idx1 - 1][idx2], len[idx1][idx2 - 1]);
      }
      len[idx1][idx2] = new_length;
    }
  }

  // get the longest sequence
  unsigned idx = len[seq1.size()][seq2.size()];
  lcs.clear();
  lcs.resize(idx);

  // and copy an example of longest back into lcs
  unsigned idx1 = seq1.size();
  unsigned idx2 = seq2.size();
  while ((idx1 > 0) && (idx2 > 0)) {

    if (seq1[idx1 - 1] == seq2[idx2 - 1]) {
      lcs[idx - 1] = seq1[idx1 - 1];
      --idx; --idx1; --idx2;
    } else if (len[idx1 - 1][idx2] > len[idx1][idx2 - 1]) {
      --idx1;
    } else {
      --idx2;
    }
  }
}

bool StateComparator::diffs_found() const {
  for (auto &cp : checkpoints) {
    if (!cp.diffs.empty()) {
      return true;
    }
  }
  return false;
}

bool StateComparator::isEquivalent() {

  if (ver2.finalState == nullptr) {
    checkpoints.emplace_back("@n/a", UINT32_MAX, UINT32_MAX, UINT32_MAX);
    auto &diffs = checkpoints.back().diffs;
    diffs.emplace_back(DiffType::delta, "@ver2", "faulting execution");
  } else if ((ver1.term_reason == TerminateReason::Return || ver1.term_reason == TerminateReason::Exit) &&
//             (ver1.term_reason != TerminateReason::Return) &&
//             (ver1.term_reason != TerminateReason::Exit) &&
             (ver1.term_reason != ver2.term_reason)) {

    ExecutionState *state = ver2.finalState;
    string fn = "@unknown";
    if (!state->stack.empty()) fn = ver2.finalState->stack.back().kf->getName();
    checkpoints.emplace_back(fn, state->stack.size(), state->linear_distance, calcStackDistance(state));

    auto &diffs = checkpoints.back().diffs;
    string element;
    switch (ver2.term_reason) {

      case TerminateReason::MemFault: {
        if (state->instFaulting != nullptr) {
          ostringstream ss;
          ss << '@' << fs::path(state->instFaulting->info->file).filename().string();
          ss << ':' << state->instFaulting->info->line;
          element = ss.str();
        } else {
          element = "@unknown";
        }
      }
      break;

      case TerminateReason::Exit: {
        element = fn;
        element += ".exit()";
      }
      break;

      case TerminateReason::Abort: {
        element = fn;
        element += ".abort()";
      }
      break;

      default: break;
    }

    if (!element.empty()) {
      ostringstream ss;
      ss << to_string(ver2.term_reason);
      if ((state->moFaulting != nullptr) && (!state->moFaulting->name.empty())) {
        ss << ':' << state->moFaulting->name;
      }
      if (!state->messages.empty()) ss << ": " << state->messages.back();
      diffs.emplace_back(DiffType::delta, element, ss.str());
    }
  } else if (test.is_main() && !test.unconstraintFlags.isUnconstrainGlobals()) {
    compareExternalState();
  } else {
    compareInternalState();
  }
  return !diffs_found();
}

bool StateComparator::compareExternalState() {

  assert(checkpoints.empty());

  // external comparison will only have a single checkpoint, at program termination
  checkpoints.emplace_back("@main", UINT32_MAX, UINT32_MAX, UINT32_MAX);
  auto &diffs = checkpoints.back().diffs;

  // each  must have a return value, it must be an int, and they must be equal
  ref<ConstantExpr> exit_expr1 = dyn_cast<ConstantExpr>(ver1.finalState->last_ret_value);
  ref<ConstantExpr> exit_expr2 = dyn_cast<ConstantExpr>(ver2.finalState->last_ret_value);

  if (!is_valid(ver1.term_reason)) return true;
  if (ver1.term_reason != ver2.term_reason) {
    diffs.emplace_back(DiffType::delta, "@post", "did not complete");

  } else if (!exit_expr1.isNull()) {
    if (exit_expr2.isNull()) {
      diffs.emplace_back(DiffType::delta, "@exit_code", "missing");
    } else {
      // if they have one value, make sure its the same (could be no value in the case of an abort)
      unsigned exit_code1 = exit_expr1->getZExtValue(Expr::Int32);
      unsigned exit_code2 = exit_expr2->getZExtValue(Expr::Int32);
      if (exit_code1 != exit_code2) {
        diffs.emplace_back(DiffType::delta, "@exit_code", "different value");
      }
    }
  }

  string stdout1 = to_data_string(ver1.finalState->stdout_capture);
  string stdout2 = to_data_string(ver2.finalState->stdout_capture);
  if (stdout1 != stdout2) {

    string out1 = to_char_string(ver1.finalState->stdout_capture);
    string out2 = to_char_string(ver2.finalState->stdout_capture);

    dtl::Diff<char, string> d(out1, out2);
    d.compose();
    ostringstream ss;
    d.printSES(ss);
    string desc = ss.str();
    replace(desc.begin(), desc.end(), '\n', ',');
    diffs.emplace_back(DiffType::delta, "@stdout", desc);
  }

  string stderr1 = to_data_string(ver1.finalState->stderr_capture);
  string stderr2 = to_data_string(ver2.finalState->stderr_capture);
  if (stderr1 != stderr2) {

    string out1 = to_char_string(ver1.finalState->stderr_capture);
    string out2 = to_char_string(ver2.finalState->stderr_capture);

    dtl::Diff<char, string> d(out1, out2);
    d.compose();
    ostringstream ss;
    d.printSES(ss);
    string desc = ss.str();
    replace(desc.begin(), desc.end(), '\n', ',');
    diffs.emplace_back(DiffType::delta, "@stderr", desc);
  }

  compareExternalCallLog(ver1.finalState, ver2.finalState);

  return !diffs_found();
}

bool StateComparator::compareInternalState() {

  assert(checkpoints.empty());

  // get the set of global variables to compare.  These are only
  // user globals (i.e. not stdlib) in both modules and of equivalent types
  set_ex<const GlobalVariable*> gbs1;
  ver1.kmodule->getUserGlobals(gbs1);
  for (const GlobalVariable *gv1 : gbs1) {

    assert(gv1 != nullptr);
    const auto &itr1 = ver1.global_map.find(gv1);
    if (itr1 != ver1.global_map.end()) {

      string name = gv1->getName();
      const GlobalVariable *gv2 = ver2.kmodule->getGlobalVariable(name);
      if (gv2 != nullptr) {

        Type *type = gv1->getType();
        // in llvm IR, all globals are pointers to their addr
        assert(type->isPointerTy());
        if (ModuleTypes::isEquivalentType(type, gv2->getType())) {
          const auto &itr2 = ver2.global_map.find(gv2);
          if (itr2 != ver2.global_map.end()) {
            globals.emplace(name, itr1->second, itr2->second, type->getPointerElementType());
          }
        }
      }
    }
  }

  if (alignFnReturns()) {

    // check each of the intermediate states.  rem that we have already verified that they are the same size
    auto itr1 = ver1.fn_returns.begin(), end1 = ver1.fn_returns.end();
    auto itr2 = ver2.fn_returns.begin();
    unsigned counter = 0;
    while (itr1 != end1) {

      string name1 = itr1->first->getName();
      string name2 = itr2->first->getName();
      assert(name1 == name2 && "mismatched function names");

      if (!(isBlacklisted(itr1->first) || isBlacklisted(itr2->first))) {
        unsigned min_distance = min(itr1->second->min_distance, itr2->second->min_distance);
        unsigned linear_distance = min(itr1->second->linear_distance, itr2->second->linear_distance);
        unsigned stack_distance = min(calcStackDistance(itr1->second), calcStackDistance(itr2->second));
        checkpoints.emplace_back(name1, min_distance, linear_distance, stack_distance);
        compareInternalState(itr1->first, itr1->second, itr2->first, itr2->second, false);
      }
      ++itr1;
      ++itr2;
      ++counter;
    }
  }

  // check the final state
  KFunction *kf1 = ver1.kmodule->getKFunction(test.entry_fn);
  KFunction *kf2 = ver2.kmodule->getKFunction(test.entry_fn);

  unsigned min_distance = min(ver1.finalState->min_distance, ver2.finalState->min_distance);
  unsigned linear_distance = min(ver1.finalState->linear_distance, ver2.finalState->linear_distance);
  unsigned stack_distance = min(calcStackDistance(ver1.finalState), calcStackDistance(ver2.finalState));
  checkpoints.emplace_back(test.entry_fn, min_distance, linear_distance, stack_distance);

  compareInternalState(kf1, ver1.finalState, kf2, ver2.finalState, true);
  return !diffs_found();
}

void StateComparator::compareInternalState(KFunction *kf1, ExecutionState *state1, KFunction *kf2, ExecutionState *state2, bool is_final) {

  assert(!checkpoints.empty());
  auto &diffs = checkpoints.back().diffs;
  assert(diffs.empty());

  Function *fn1 = kf1->function;
  Function *fn2 = kf2->function;

  KFunction *last_kf1 = nullptr;
  if (state1->stack.size() > 0) {
    last_kf1 = state1->stack.back().kf;
  }
  KFunction *last_kf2 = nullptr;
  if (state2->stack.size() > 0) {
    last_kf2= state2->stack.back().kf;
  }
  if (last_kf1 && last_kf2 && last_kf1->getName() == last_kf2->getName()) {

    // check the return value
    Type *type = fn1->getReturnType();
    if (!type->isVoidTy() && ModuleTypes::isEquivalentType(type, fn2->getReturnType())) {
      // state1 may lack a return value due to an abort
      if (!state1->last_ret_value.isNull()) {
        // if state1 has a return value, then state2 must have one as well
        if (!state2->last_ret_value.isNull()) {
          ref<ConstantExpr> ret1 = dyn_cast<ConstantExpr>(state1->last_ret_value);
          ref<ConstantExpr> ret2 = dyn_cast<ConstantExpr>(state2->last_ret_value);
          assert(!(ret1.isNull() || ret2.isNull()));
          visited_ptrs.clear();
          compareRetExprs(ret1, kf1, state1, ret2, kf2, state2, type);
        } else {
          string element = kf1->getName();
          element +=".@return";
          diffs.emplace_back(DiffType::delta, element, "missing return value");
        }
      }
    }

    // scan for pointer parameters - these could be outputs
    if (!kf1->isDiffChangedSig() && !fn1->isVarArg()) {
      unsigned idx = 0;
      for (auto itr = fn1->arg_begin(), end = fn1->arg_end(); itr != end; ++itr) {
        Argument &arg = *itr;
        if (auto *arg_type = dyn_cast<PointerType>(arg.getType())) {
          string name = kf1->getName();
          name += ".@";
          if (arg.hasName()) name += arg.getName();
          else name += std::to_string(idx);

          ref<Expr> expr1 = state1->stack.back().locals[kf1->getArgRegister(idx)].value;
          if (!expr1.isNull()) {
            ref<ConstantExpr> ptr1 = dyn_cast<ConstantExpr>(expr1);
            if (!ptr1.isNull()) {
              ref<Expr> expr2 = state2->stack.back().locals[kf2->getArgRegister(idx)].value;
              if (!expr2.isNull()) {
                ref<ConstantExpr> ptr2 = dyn_cast<ConstantExpr>(expr2);
                if (!ptr2.isNull()) {
                  comparePtrs(ptr1, kf1, state1, ptr2, kf2, state2, name, arg_type);
                } else {
                  diffs.emplace_back(DiffType::delta, name, "ptr did not evaluate to a constant");
                }
              } else {
                diffs.emplace_back(DiffType::delta, name, "missing ptr value");
              }
            }
          }
        }
        idx += 1;
      }
    }
  }

  // if this is not the final state or both fns returned, then check user global variables
  // if they did not return, no further execution is possible and no further behavior.
  if (!is_final || ((ver1.term_reason == TerminateReason::Return) && (ver2.term_reason == TerminateReason::Return))) {
    for (auto itr = globals.begin(), end = globals.end(); itr != end; ++itr) {
      const CompareGlobalEntry &entry = *itr;
      visited_ptrs.clear();
      compareMemoryObjects(entry.mo1, kf1, state1, entry.mo2, kf2, state2, entry.name, entry.type);
    }
  }

  // check output devices
  string stdout1 = to_data_string(state1->stdout_capture);
  string stdout2 = to_data_string(state2->stdout_capture);
  if (stdout1 != stdout2) {

    string out1 = to_char_string(state1->stdout_capture);
    string out2 = to_char_string(state2->stdout_capture);

    dtl::Diff<char, string> d(out1, out2);
    d.compose();
    ostringstream ss;
    d.printSES(ss);
    string desc = ss.str();
    replace(desc.begin(), desc.end(), '\n', ',');
    if (desc.size() > 80) {
      desc = desc.substr(0, 80);
    }
    diffs.emplace_back(DiffType::delta, "@stdout", desc);
  }

  string stderr1 = to_data_string(state1->stderr_capture);
  string stderr2 = to_data_string(state2->stderr_capture);
  if (stderr1 != stderr2) {

    string out1 = to_char_string(state1->stderr_capture);
    string out2 = to_char_string(state2->stderr_capture);

    dtl::Diff<char, string> d(out1, out2);
    d.compose();
    ostringstream ss;
    d.printSES(ss);
    string desc = ss.str();
    replace(desc.begin(), desc.end(), '\n', ',');
    diffs.emplace_back(DiffType::delta, "@stderr", desc);
  }

  compareExternalCallLog(state1, state2);
}

void StateComparator::compareExternalCallLog(ExecutionState *state1, ExecutionState *state2) {

  assert(!checkpoints.empty());
  auto &diffs = checkpoints.back().diffs;

  // find set of external call in common
  map<string, Function *> externs1, externs2;

  for (auto &call : state1->extern_call_log) {
    Function *fn = call.first;
    externs1.insert(make_pair(fn->getName(), fn));
  }
  for (auto &call : state2->extern_call_log) {
    Function *fn = call.first;
    externs2.insert(make_pair(fn->getName(), fn));
  }

  for (const auto &itr1 : externs1) {
    const string &name = itr1.first;
    const auto &itr2 = externs2.find(name);
    if (itr2 == externs2.end()) {
      // state2 did not call this function
      diffs.emplace_back(DiffType::delta, itr1.first, "not called by state1");
    } else {
      Function *fn1 = itr1.second;
      Function *fn2 = itr2->second;
      if (ModuleTypes::isEquivalentType(fn1->getFunctionType(), fn2->getFunctionType())) {
        compareExternalCallFn(fn1, state1, fn2, state2);
      }
      externs2.erase(itr2);
    }
  }

  // anything left in externs2 was not called by state1
  for (const auto &itr : externs2) {
    diffs.emplace_back(DiffType::delta, itr.first, "not called by state2");
  }
}

void StateComparator::compareExternalCallFn(llvm::Function *fn1, ExecutionState *state1, llvm::Function *fn2,
                                            ExecutionState *state2) {

  vector<vector<ref<Expr>> *> args1, args2;
  for (auto &call : state1->extern_call_log) {
    if (call.first == fn1) {
      args1.push_back(&call.second);
    }
  }

  for (auto &call : state2->extern_call_log) {
    if (call.first == fn2) {
      args2.push_back(&call.second);
    }
  }
  if (args1.size() != args2.size()) {
    assert(!checkpoints.empty());
    auto &diffs = checkpoints.back().diffs;
    diffs.emplace_back(DiffType::delta, fn1->getName(), "unmatched calls");
  } else {
    for (unsigned idx = 0, end = args1.size(); idx < end; ++idx) {
      // fn1 and fn2 are type equivalent, so we can use either one
      compareExternalCallArgs(fn1, *args1[idx], *args2[idx]);
    }
  }
}

void StateComparator::compareExternalCallArgs(llvm::Function *fn, const vector<ref<Expr>> &args1, const vector<ref<Expr>> &args2) {

  assert(!checkpoints.empty());
  auto &diffs = checkpoints.back().diffs;
  unsigned idx = 0;
  for (auto itr = fn->arg_begin(), end = fn->arg_end(); itr != end; ++itr) {
    Type *type = itr->getType();
    if (!type->isVoidTy() && (type->isPrimitiveType() || type->isIntegerTy())) {
      ref<ConstantExpr> expr1 = dyn_cast<ConstantExpr>(args1[idx]);
      ref<ConstantExpr> expr2 = dyn_cast<ConstantExpr>(args2[idx]);
      if (!expr1.isNull() && !expr2.isNull()) {
        if (expr1->getAPValue() != expr2->getAPValue()) {
          diffs.emplace_back(DiffType::delta, fn->getName(), "different arg value");
        }
      }
    }
    ++idx;
  }
}

void StateComparator::compareObjectStates(const ObjectState *os1, uint64_t offset1, KFunction *kf1, ExecutionState *state1,
                                          const ObjectState *os2, uint64_t offset2, KFunction *kf2, ExecutionState *state2,
                                          const string &name, llvm::Type *type) {

  assert(!checkpoints.empty());
  auto &diffs = checkpoints.back().diffs;

  assert(!type->isVoidTy());

  if (!isBlacklisted(type)) {
    if (type->isSingleValueType()) {

      if (type->isPointerTy()) {

        // pointer comparison
        ref<ConstantExpr> ptr1 = dyn_cast<ConstantExpr>(os1->read(offset1, ptr_width));
        ref<ConstantExpr> ptr2 = dyn_cast<ConstantExpr>(os2->read(offset2, ptr_width));
        assert(!(ptr1.isNull() || ptr2.isNull()));
        comparePtrs(ptr1, kf1, state1, ptr2, kf2, state2, name, cast<PointerType>(type));

      } else {

        // primitive type. just do a raw comparison
        unsigned size = datalayout->getTypeStoreSize(type);
        vector<unsigned char> val1, val2;
        os1->readConcreteStore(val1, offset1, size);
        os2->readConcreteStore(val2, offset2, size);
        if (val1 != val2) {
          diffs.emplace_back(DiffType::delta, name, "different value");
        }
      }
    } else if (type->isStructTy()) {
      auto *stype = cast<StructType>(type);

      // recursively compare each field in the structure
      const StructLayout *sl = datalayout->getStructLayout(stype);
      for (unsigned idx = 0, end = stype->getNumElements(); idx != end; ++idx) {
        Type *etype = stype->getElementType(idx);
        unsigned eoffset = sl->getElementOffset(idx);
        string field_name = '{' + name + ':' + std::to_string(idx) + '}';
        compareObjectStates(os1, offset1 + eoffset, kf1, state1, os2, offset2 + eoffset, kf2, state2, field_name, etype);
      }

    } else if (type->isVectorTy()) {
      auto *vtype = cast<VectorType>(type);

      // until shown otherwise, just treat vectors like arrays
      Type *etype = vtype->getElementType();
      unsigned esize = datalayout->getTypeStoreSize(etype);
      unsigned eoffset = 0;
      for (unsigned idx = 0, end = etype->getVectorNumElements(); idx != end; ++idx) {
//        string index_name = '[' + name + ':' + std::to_string(idx) + ']';
        string index_name = name;
        compareObjectStates(os1, offset1 + eoffset, kf1, state1, os2, offset2 + eoffset, kf2, state2, index_name, etype);
        eoffset += esize;
      }

    } else if (type->isArrayTy()) {
      auto *atype = cast<ArrayType>(type);

      // iteratively check each array element
      Type *etype = atype->getElementType();
      unsigned esize = datalayout->getTypeStoreSize(etype);
      unsigned eoffset = 0;
      for (unsigned idx = 0, end = atype->getArrayNumElements(); idx != end; ++idx) {
//        string index_name = '[' + name + ':' + std::to_string(idx) + ']';
        string index_name = name;
        compareObjectStates(os1, offset1 + eoffset, kf1, state1, os2, offset2 + eoffset, kf2, state2, index_name, etype);
        eoffset += esize;
      }

    } else if (type->isFunctionTy()) {
      auto *ftype = cast<FunctionType>(type);
      (void) ftype;
      assert("function type should never occur here");
    }
  }
}

void StateComparator::compareMemoryObjects(const MemoryObject *mo1, uint64_t offset1, KFunction *kf1, ExecutionState *state1,
                                           const MemoryObject *mo2, uint64_t offset2, KFunction *kf2, ExecutionState *state2,
                                           const string &name, llvm::Type *type) {

  assert(!checkpoints.empty());
  auto &diffs = checkpoints.back().diffs;

  if (!isBlacklisted(type)) {
    if (!type->isVoidTy()) {
      if (const ObjectState *os1 = state1->addressSpace.findObject(mo1)) {
        const ObjectState *os2 = state2->addressSpace.findObject(mo2);
        if (os2 == nullptr) {
          diffs.emplace_back(DiffType::delta, name, "unable to find memory object");
        } else {
          compareObjectStates(os1, offset1, kf1, state1, os2, offset2, kf2, state2, name, type);
        }
      }
    }
  }
}

void StateComparator::compareRetExprs(const ref<ConstantExpr> &expr1, KFunction *kf1, ExecutionState *state1,
                                      const ref<ConstantExpr> &expr2, KFunction *kf2, ExecutionState *state2,
                                      llvm::Type *type) {

  assert(!checkpoints.empty());
  auto &diffs = checkpoints.back().diffs;
  if (!isBlacklisted(type)) {
    if (!type->isVoidTy()) {
      if (type->isSingleValueType()) {
        string name = kf1->getName();
        name += ".@return";
        if (type->isPointerTy()) {

          // pointer comparison
          comparePtrs(expr1, kf1, state1, expr2, kf2, state2, name, cast<PointerType>(type));
        } else {

          // these are supposed to fit in a single register
          // since this is not a pointer value, they can be directly compared
          Expr::Width width = expr1->getWidth();
          if (expr2->getWidth() != width) {
            diffs.emplace_back(DiffType::delta, name, "different width");
          } else {
            // most of these types are no more than 64 bits.
            if (width <= Expr::Int64) {
              if (expr1->getZExtValue() != expr2->getZExtValue()) {
                diffs.emplace_back(DiffType::delta, name, "different value");
              }
            } else if (width == Expr::Fl80) {

              unsigned char val1[Expr::Fl80 / 8];
              unsigned char val2[Expr::Fl80 / 8];
              expr1->toMemory(val1);
              expr2->toMemory(val2);
              if (memcmp(val1, val2, Expr::Fl80 / 8) != 0) {
                diffs.emplace_back(DiffType::delta, name, "different value");
              }
            } else {
              klee_error("unsupported expr width");
            }
          }
        }
      } else {
        assert("multi-value types should not occur as expressions");
      }
    }
  }
}

void StateComparator::comparePtrs(const ref<klee::ConstantExpr> &expr1, KFunction *kf1, ExecutionState *state1,
                                  const ref<klee::ConstantExpr> &expr2, KFunction *kf2, ExecutionState *state2,
                                  const std::string &name, PointerType *type) {

  assert(!checkpoints.empty());
  auto &diffs = checkpoints.back().diffs;
  if (!isBlacklisted(type)) {
    if (expr1->getWidth() != expr2->getWidth()) {
      diffs.emplace_back(DiffType::delta, name, "incompatible pointer widths");
    } else {
      uint64_t addr1 = expr1->getZExtValue();
      uint64_t addr2 = expr2->getZExtValue();
      comparePtrs(addr1, kf1, state1, addr2, kf2, state2, name, type);
    }
  }
}

void StateComparator::comparePtrs(uint64_t addr1, KFunction *kf1, ExecutionState *state1,
                                  uint64_t addr2, KFunction *kf2, ExecutionState *state2,
                                  const std::string &name, PointerType *type) {

  assert(!checkpoints.empty());
  auto &diffs = checkpoints.back().diffs;
  if (!isBlacklisted(type)) {

    if (addr1 == 0) {
      if (addr2 != 0) {
        diffs.emplace_back(DiffType::delta, name, "pointer is not null");
      }
    } else {
      // addr1 is not zero, so it must point to an object
      if (addr2 == 0) {
        diffs.emplace_back(DiffType::delta, name, "pointer is null");
      } else {
        // neither pointer is null, so both must point to objects
        // do not recurse through the same pointer pair twice, prevents pointer cycles from looping forever
        auto result = visited_ptrs.insert(make_pair(addr1, addr2));
        if (result.second) {

          ObjectPair op1;
          if (state1->addressSpace.resolveOne(addr1, op1)) {
            ObjectPair op2;
            if (state2->addressSpace.resolveOne(addr2, op2)) {

              // RLR TODO: check memkind?

              // if this is a heap allocation, then may be a sequence of objects
              Type *pted_type = type->getPointerElementType();
              if (op1.first->isHeap()) {
                if (op1.second->visible_size != op2.second->visible_size) {
                  diffs.emplace_back(DiffType::delta, name, "different dynamic allocation sizes");
                  return;
                }
                unsigned size = datalayout->getTypeStoreSize(pted_type);
                unsigned count = op1.second->visible_size / size;
                pted_type = ArrayType::get(pted_type, count);
              }

              uint64_t offset1 = addr1 - op1.first->address;
              uint64_t offset2 = addr2 - op2.first->address;
              string ptr_name = "*(" + name + ')';
              compareObjectStates(op1.second, offset1, kf1, state1, op2.second, offset2, kf2, state2, ptr_name, pted_type);

            } else {
              diffs.emplace_back(DiffType::delta, name, "unable to find referenced object");
            }
          }
        }
      }
    }
  }
}

unsigned StateComparator::calcStackDistance(const ExecutionState *state) {

  assert(state != nullptr);
  unsigned result = 0;
  for (auto ritr = state->stack.rbegin(), rend = state->stack.rend(); ritr != rend; ++ritr) {
    const StackFrame &sf = *ritr;
    if (sf.kf->isDiffChanged()) {
      break;
    }
    result += 1;
  }
  return result;
}

} // end klee namespace
