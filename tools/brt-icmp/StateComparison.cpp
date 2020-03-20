//
//
//
// Created by rrutledge on 10/23/19.
//

#include "StateComparison.h"
#include <vector>

#include "llvm/IR/DataLayout.h"
#include "llvm/Support/raw_ostream.h"
#include "klee/Internal/System/Memory.h"
#include "klee/Internal/Module/Cell.h"

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

std::string to_string(const CompareDiff &diff) {

  static const char type_designators[] = { 'I', 'D', 'I', 'W', 'F' };
  ostringstream ss;

  ss << type_designators[(unsigned) diff.type] << ';';
  if (diff.distance == UINT_MAX) ss << "+;";
  else ss << diff.distance << ';';
  ss << diff.fn << ';' << diff.element << ';' << diff.desc;
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

StateComparator::StateComparator(const TestCase &t, StateVersion &v1, StateVersion &v2) :
  test(t), ver1(v1), ver2(v2), datalayout(ver1.kmodule->targetData) {

  ptr_width = datalayout->getPointerSizeInBits();
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
    result = ver2.finalState->instFaulting;
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

  // only continue if the function call returns are comparable, i.e. they are aligned
  //  RLR TODO: if not aligned, try to align them
  if (ver1.fn_returns.size() != ver2.fn_returns.size()) {

    CompareDiff diff(DiffType::warning);
    diff.fn = "@unaligned";
    diff.distance = UINT_MAX;

    ostringstream ss;
    emitRetSequence(ss, ver1.fn_returns);
    ss << ':';
    emitRetSequence(ss, ver2.fn_returns);
    diff.desc = ss.str();

    diffs.emplace_back(diff);
    return false;
  }
  auto itr1 = ver1.fn_returns.begin(), end1 = ver1.fn_returns.end();
  auto itr2 = ver2.fn_returns.begin();
  while (itr1 != end1) {
    if (itr1->first->getName() != itr2->first->getName()) {
      CompareDiff diff(DiffType::warning);
      diff.fn = "@unaligned";
      diff.distance = UINT_MAX;

      ostringstream ss;
      emitRetSequence(ss, ver1.fn_returns);
      ss << ':';
      emitRetSequence(ss, ver2.fn_returns);
      diff.desc = ss.str();

      diffs.emplace_back(diff);
      return false;
    }
    ++itr1; ++itr2;
  }
  return true;
}

void StateComparator::emitRetSequence(std::ostringstream &ss, std::deque<std::pair<KFunction*, ExecutionState*> > &fn_returns) {

  bool first = true;
  for (auto &pr : fn_returns) {
    if (first) first = false;
    else ss << ',';
    ss << pr.first->getName();
  }
}

bool StateComparator::isEquivalent() {

  bool result = false;
  if (ver2.finalState == nullptr) {
    CompareDiff diff(DiffType::delta);
    diff.fn = diff.element = "@unknown";
    diff.desc = "incomplete execution";
    if (test.is_main()) diff.distance = UINT_MAX;
    diffs.emplace_back(diff);
  } else if ((ver1.term_reason == TerminateReason::Return || ver1.term_reason == TerminateReason::Exit) &&
             (ver1.term_reason != ver2.term_reason)) {
    ExecutionState *state = ver2.finalState;
    CompareDiff diff(DiffType::delta);
    diff.fn = diff.element = "@unknown";
    diff.desc = to_string(ver2.term_reason);
    if (!state->messages.empty()) diff.desc += '-' + state->messages.back();
    if (!state->stack.empty()) diff.fn = ver2.finalState->stack.back().kf->getName();
    if (state->instFaulting != nullptr) diff.element = std::to_string(state->instFaulting->info->assemblyLine);
    diff.distance = test.is_main() ? UINT_MAX : state->distance;
    diffs.emplace_back(diff);
  } else if (test.is_main() && !test.unconstraintFlags.isUnconstrainGlobals()) {
    result = compareExternalState();
  } else {
    result = compareInternalState();
  }
  return result;
}

bool StateComparator::compareExternalState() {

  assert(diffs.empty());

  // each  must have a return value, it must be an int, and they must be equal
  ref<ConstantExpr> exit_expr1 = dyn_cast<ConstantExpr>(ver1.finalState->last_ret_value);
  ref<ConstantExpr> exit_expr2 = dyn_cast<ConstantExpr>(ver2.finalState->last_ret_value);

  if (!is_valid(ver1.term_reason)) return true;
  if (ver1.term_reason != ver2.term_reason) {
    diffs.emplace_back(CompareExtDiff("@post", "did not complete"));

  } else if (!exit_expr1.isNull()) {
    if (exit_expr2.isNull()) {
      diffs.emplace_back(CompareExtDiff("@exit_code", "missing"));
    } else {
      // if they have one value, make sure its the same (could be no value in the case of an abort)
      unsigned exit_code1 = exit_expr1->getZExtValue(Expr::Int32);
      unsigned exit_code2 = exit_expr2->getZExtValue(Expr::Int32);
      if (exit_code1 != exit_code2) {
        diffs.emplace_back(CompareExtDiff("@exit_code", "different value"));
      }
    }
  }

  string stdout1 = to_string(ver1.finalState->stdout_capture);
  string stdout2 = to_string(ver2.finalState->stdout_capture);
  if (stdout1 != stdout2) {
    diffs.emplace_back(CompareExtDiff("@stdout", "different output"));
  }

  string stderr1 = to_string(ver1.finalState->stderr_capture);
  string stderr2 = to_string(ver2.finalState->stderr_capture);
  if (stderr1 != stderr2) {
    diffs.emplace_back(CompareExtDiff("@stderr", "different output"));
  }
  return (size_diffs() == 0);
}

bool StateComparator::compareInternalState() {

  assert(diffs.empty());

  // get the set of global variables to compare.  These are only
  // user globals (i.e. not stdlib) in both modules and of equivalent types
  set<const GlobalVariable*> gbs1;
  ver1.kmodule->getUserGlobals(gbs1);
  for (const GlobalVariable *gv1 : gbs1) {

    assert(gv1 != nullptr);
    const auto &itr1 = ver1.global_map.find(gv1);
    if (itr1 != ver1.global_map.end()) {

      string name = gv1->getName();
      const GlobalVariable *gv2 = ver2.kmodule->getGlobalVariable(name);
      if (gv2 != nullptr) {

        Type *type = gv1->getType();
        // in llvm, all globals are pointers to their addr
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
        compareInternalState(itr1->first, itr1->second, itr2->first, itr2->second);
      }
      ++itr1; ++itr2; ++counter;
    }
  }

  // check the final state
  KFunction *kf1 = ver1.kmodule->getKFunction(test.entry_fn);
  KFunction *kf2 = ver2.kmodule->getKFunction(test.entry_fn);
  compareInternalState(kf1, ver1.finalState, kf2, ver2.finalState);
  return (size_diffs() == 0);
}

bool StateComparator::compareInternalState(KFunction *kf1, ExecutionState *state1, KFunction *kf2, ExecutionState *state2) {

  Function *fn1 = kf1->function;
  Function *fn2 = kf2->function;
  size_t diff_count = size_diffs();

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
        diffs.emplace_back(CompareIntDiff(kf2, "@return", state2, "missing return value"));
      }
    }
  }

  // scan for pointer parameters - these could be outputs
  if (!kf1->isDiffChangedSig() && !fn1->isVarArg()) {
    unsigned idx = 0;
    for (auto itr = fn1->arg_begin(), end = fn1->arg_end(); itr != end; ++itr) {
      Argument &arg = *itr;
      if (auto *arg_type = dyn_cast<PointerType>(arg.getType())) {
        string name;
        if (arg.hasName()) name = arg.getName();
        else name = std::to_string(idx);

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
                diffs.emplace_back(CompareIntDiff(kf2, name, state2, "ptr did not evaluate to a constant"));
              }
            } else {
              diffs.emplace_back(CompareIntDiff(kf2, name, state2, "missing ptr value"));
            }
          }
        }
      }
      idx += 1;
    }
  }

  // check output devices
  string stdout1 = to_string(state1->stdout_capture);
  string stdout2 = to_string(state2->stdout_capture);
  if (stdout1 != stdout2) {
    diffs.emplace_back(CompareIntDiff(kf1, "@stdout", state2, "different output"));
  }

  string stderr1 = to_string(state1->stderr_capture);
  string stderr2 = to_string(state2->stderr_capture);
  if (stderr1 != stderr2) {
    diffs.emplace_back(CompareIntDiff(kf1, "@stderr", state2, "different output"));
  }

  // finally, check user global variables
  for (auto itr = globals.begin(), end = globals.end(); itr != end; ++itr) {
    const CompareGlobalEntry &entry = *itr;
    visited_ptrs.clear();
    if (!compareMemoryObjects(entry.mo1, kf1, state1, entry.mo2, kf2, state2, entry.name, entry.type)) {
      itr = globals.erase(itr);
    }
  }
  return (size_diffs() == diff_count);
}

bool StateComparator::compareObjectStates(const ObjectState *os1, uint64_t offset1, KFunction *kf1, ExecutionState *state1,
                                          const ObjectState *os2, uint64_t offset2, KFunction *kf2, ExecutionState *state2,
                                          const string &name, llvm::Type *type) {

  assert(!type->isVoidTy());
  size_t diff_count = size_diffs();

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
        os1->readConcrete(val1, offset1, size);
        os2->readConcrete(val2, offset2, size);
        if (val1 != val2) {
          diffs.emplace_back(CompareIntDiff(kf2, name, state2, "different value"));
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
        string index_name = '[' + name + ':' + std::to_string(idx) + ']';
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
        string index_name = '[' + name + ':' + std::to_string(idx) + ']';
        compareObjectStates(os1, offset1 + eoffset, kf1, state1, os2, offset2 + eoffset, kf2, state2, index_name, etype);
        eoffset += esize;
      }

    } else if (type->isFunctionTy()) {
      auto *ftype = cast<FunctionType>(type);
      (void) ftype;
      assert("function type should never occur here");
    }
  }
  return (size_diffs() == diff_count);
}

bool StateComparator::compareMemoryObjects(const MemoryObject *mo1, uint64_t offset1, KFunction *kf1, ExecutionState *state1,
                                           const MemoryObject *mo2, uint64_t offset2, KFunction *kf2, ExecutionState *state2,
                                           const string &name, llvm::Type *type) {

  size_t diff_count = size_diffs();
  if (!isBlacklisted(type)) {
    if (!type->isVoidTy()) {
      if (const ObjectState *os1 = state1->addressSpace.findObject(mo1)) {
        const ObjectState *os2 = state2->addressSpace.findObject(mo2);
        if (os2 == nullptr) {
          diffs.emplace_back(CompareIntDiff(kf2, name, state2, "unable to find memory object"));
        } else {
          compareObjectStates(os1, offset1, kf1, state1, os2, offset2, kf2, state2, name, type);
        }
      }
    }
  }
  return (size_diffs() == diff_count);
}

bool StateComparator::compareRetExprs(const ref<ConstantExpr> &expr1, KFunction *kf1, ExecutionState *state1,
                                      const ref<ConstantExpr> &expr2, KFunction *kf2, ExecutionState *state2,
                                      llvm::Type *type) {

  size_t diff_count = size_diffs();
  if (!isBlacklisted(type)) {
    if (!type->isVoidTy()) {
      if (type->isSingleValueType()) {
        string name = "@return";
        if (type->isPointerTy()) {

          // pointer comparison
          comparePtrs(expr1, kf1, state1, expr2, kf2, state2, name, cast<PointerType>(type));
        } else {

          // these are supposed to fit in a single register
          // since this is not a pointer value, they can be directly compared
          Expr::Width width = expr1->getWidth();
          if (expr2->getWidth() != width) {
            diffs.emplace_back(CompareIntDiff(kf2, name, state2, "different width"));
          } else {
            // most of these types are no more than 64 bits.
            if (width <= Expr::Int64) {
              if (expr1->getZExtValue() != expr2->getZExtValue()) {
                diffs.emplace_back(CompareIntDiff(kf2, name, state2, "different value"));
              }
            } else {
              // this is a real hack to deal with bit-long expressions
              long double val1, val2;
              expr1->toMemory(&val1);
              expr2->toMemory(&val2);
              if (val1 != val2) {
                diffs.emplace_back(CompareIntDiff(kf2, name, state2, "different value"));
              }
            }
          }
        }
      } else {
        assert("multi-value types should not occur as expressions");
      }
    }
  }
  return (size_diffs() == diff_count);
}

bool StateComparator::comparePtrs(const ref<klee::ConstantExpr> &expr1, KFunction *kf1, ExecutionState *state1,
                                  const ref<klee::ConstantExpr> &expr2, KFunction *kf2, ExecutionState *state2,
                                  const std::string &name, PointerType *type) {

  size_t diff_count = size_diffs();
  if (!isBlacklisted(type)) {
    if (expr1->getWidth() != expr2->getWidth()) {
      diffs.emplace_back(CompareIntDiff(kf2, name, state2, "incompatible pointer widths"));
    } else {
      uint64_t addr1 = expr1->getZExtValue();
      uint64_t addr2 = expr2->getZExtValue();
      comparePtrs(addr1, kf1, state1, addr2, kf2, state2, name, type);
    }
  }
  return (size_diffs() == diff_count);
}

bool StateComparator::comparePtrs(uint64_t addr1, KFunction *kf1, ExecutionState *state1,
                                  uint64_t addr2, KFunction *kf2, ExecutionState *state2,
                                  const std::string &name, PointerType *type) {

  size_t diff_count = size_diffs();
  if (!isBlacklisted(type)) {
    // do not recurse through the same pointer pair twice, prevents pointer cycles from looping forever
    auto result = visited_ptrs.insert(make_pair(addr1, addr2));
    if (result.second) {

      ObjectPair op1;
      if (state1->addressSpace.resolveOne(addr1, op1)) {
        ObjectPair op2;
        if (state2->addressSpace.resolveOne(addr2, op2)) {

          uint64_t offset1 = addr1 - op1.first->address;
          uint64_t offset2 = addr2 - op2.first->address;
          string ptr_name = "*(" + name + ')';
          compareObjectStates(op1.second, offset1, kf1, state1, op2.second, offset2, kf2, state2, ptr_name, type->getPointerElementType());

        } else {
          diffs.emplace_back(CompareIntDiff(kf2, name, state2, "unable to find pointed object"));
        }
      }
    }
  }
  return (size_diffs() == diff_count);
}

} // end klee namespace
