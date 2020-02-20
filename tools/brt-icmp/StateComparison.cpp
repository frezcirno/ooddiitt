//
// Created by rrutledge on 10/23/19.
//

#include "StateComparison.h"
#include <vector>

#include "llvm/IR/DataLayout.h"
#include "llvm/Support/raw_ostream.h"
#include "klee/Internal/System/Memory.h"

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

StateVersion::~StateVersion() {

  // modules are deleted explicitly
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

bool StateComparator::alignFnReturns() {

  if (!test.is_main()) {
    if (ver1.fn_returns.size() != ver2.fn_returns.size()) return false;
    auto itr1 = ver1.fn_returns.begin(), end1 = ver1.fn_returns.end();
    auto itr2 = ver2.fn_returns.begin(), end2 = ver2.fn_returns.end();
    while (itr1 != end1) {
      if (itr1->first->getName() != itr2->first->getName()) return false;
      ++itr1; ++itr2;
    }
  }
  return true;
}

void StateComparator::doCompare() {

  if (test.is_main()) {
    compareExternalState();
  } else {
    compareInternalState();
  }
}

void StateComparator::compareExternalState() {

  // each  must have a return value, it must be an int, and they must be equal
  ref<ConstantExpr> exit_expr1 = dyn_cast<ConstantExpr>(ver1.finalState->last_ret_value);
  ref<ConstantExpr> exit_expr2 = dyn_cast<ConstantExpr>(ver2.finalState->last_ret_value);

  if (exit_expr1.isNull() || exit_expr2.isNull()) {
    diffs.emplace_back("missing exit code");
  } else {
    // if they have one value, make sure its the same (could be no value in the case of an abort)
    unsigned exit_code1 = exit_expr1->getZExtValue(Expr::Int32);
    unsigned exit_code2 = exit_expr2->getZExtValue(Expr::Int32);
    if (exit_code1 != exit_code2) {
      diffs.emplace_back("different return value");
    }
  }

  string stdout1 = to_string(ver1.finalState->stdout_capture);
  string stdout2 = to_string(ver2.finalState->stdout_capture);
  if (stdout1 != stdout2) {
    diffs.emplace_back("different stdout");
  }

  string stderr1 = to_string(ver1.finalState->stderr_capture);
  string stderr2 = to_string(ver2.finalState->stderr_capture);
  if (stderr1 != stderr2) {
    diffs.emplace_back("different stderr");
  }
}

void StateComparator::compareInternalState() {

  if (ver1.fn_returns.size() != ver2.fn_returns.size()) {
    diffs.emplace_back("mismatched count of return states");
  } else {

    // get the set of global variables to compare.  These are only
    // user globals (i.e. not stdlib) in both modules and of equivalent types
    set<const GlobalVariable*> gbs1;
    ver1.kmodule->getUserGlobals(gbs1);
    globals.reserve(gbs1.size());
    for (const GlobalVariable *gv1 : gbs1) {

      assert(gv1 != nullptr);
      const auto &itr1 = ver1.global_map.find(gv1);
      if (itr1 != ver1.global_map.end()) {

        const GlobalVariable *gv2 = ver2.kmodule->getGlobalVariable(gv1->getName());
        if (gv2 != nullptr) {

          Type *type = gv1->getType();
          // in llvm, all globals are pointers to their addr
          assert(type->isPointerTy());
          if (isEquivalentType(type, gv2->getType())) {
            const auto &itr2 = ver2.global_map.find(gv2);
            if (itr2 != ver2.global_map.end()) {
              globals.emplace_back(itr1->second, itr2->second, type->getPointerElementType());
            }
          }
        }
      }
    }

    // check each of the intermediate states.  rem that we have already verified that they are the same size
    auto itr1 = ver1.fn_returns.begin(), end1 = ver1.fn_returns.end();
    auto itr2 = ver2.fn_returns.begin(), end2 = ver2.fn_returns.end();
    while (itr1 != end1) {

      if (itr1->first->getName() != itr2->first->getName()) {
        diffs.emplace_back("function name mismatch in return trace");
      } else {
        compareInternalState(itr1->first, itr1->second, itr2->first, itr2->second);
      }
      ++itr1; ++itr2;
    }

    // check the final state
    KFunction *kf1 = ver1.kmodule->getKFunction(test.entry_fn);
    KFunction *kf2 = ver2.kmodule->getKFunction(test.entry_fn);
    compareInternalState(kf1, ver1.finalState, kf2, ver2.finalState);
  }
}

void StateComparator::compareInternalState(KFunction *kf1, ExecutionState *state1, KFunction *kf2, ExecutionState *state2) {

  Function *fn1 = kf1->function;
  Function *fn2 = kf2->function;

  // check the return value
  Type *type = fn1->getReturnType();
  if (!type->isVoidTy() && isEquivalentType(type, fn2->getReturnType())) {

    ref<ConstantExpr> ret1 = dyn_cast<ConstantExpr>(state1->last_ret_value);
    ref<ConstantExpr> ret2 = dyn_cast<ConstantExpr>(state2->last_ret_value);
    assert(!(ret1.isNull() || ret2.isNull()));
    visited_ptrs.clear();
    compareExprs(ret1, state1, ret2, state2, type);
  } else {
    diffs.emplace_back("incomparable return types");
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
    visited_ptrs.clear();
    compareMemoryObjects(entry.mo1, state1, entry.mo2, state2, entry.type);
  }
}

void StateComparator::compareObjectStates(const ObjectState *os1, uint64_t offset1, ExecutionState *state1,
                                          const ObjectState *os2, uint64_t offset2, ExecutionState *state2,
                                          llvm::Type *type) {

  assert(!type->isVoidTy());
  if (type->isSingleValueType()) {

    if (type->isPointerTy()) {

      // pointer comparison
      ref<ConstantExpr> ptr1 = dyn_cast<ConstantExpr>(os1->read(offset1, ptr_width));
      ref<ConstantExpr> ptr2 = dyn_cast<ConstantExpr>(os2->read(offset2, ptr_width));
      assert(!(ptr1.isNull() || ptr2.isNull()));
      comparePtrs(ptr1, state1, ptr2, state2, cast<PointerType>(type));

    } else {

      // primative type. just do a raw comparison
      unsigned size = datalayout->getTypeStoreSize(type);
      vector<unsigned char> val1, val2;
      os1->readConcrete(val1, offset1, size);
      os2->readConcrete(val2, offset2, size);
      if (val1 != val2) {
        diffs.emplace_back("different single mo value");
      }
    }
  } else if (type->isStructTy()) {
    auto *stype = cast<StructType>(type);

    // recursively compare each field in the structure
    const StructLayout *sl = datalayout->getStructLayout(stype);
    for (unsigned idx = 0, end = stype->getNumElements(); idx != end; ++idx) {
      Type *etype = stype->getElementType(idx);
      unsigned eoffset = sl->getElementOffset(idx);
      compareObjectStates(os1, offset1 + eoffset, state1, os2, offset2 + eoffset, state2, etype);
    }

  } else if (type->isVectorTy()) {
    auto *vtype = cast<VectorType>(type);

    // until shown otherwise, just treat vectors like arrays
    Type *etype = vtype->getElementType();
    unsigned esize = datalayout->getTypeStoreSize(etype);
    unsigned eoffset = 0;
    for (unsigned idx = 0, end = etype->getVectorNumElements(); idx != end; ++idx) {
      compareObjectStates(os1, offset1 + eoffset, state1, os2, offset2 + eoffset, state2, etype);
      eoffset += esize;
    }

  } else if (type->isArrayTy()) {
    auto *atype = cast<ArrayType>(type);

    // iteratively check each array element
    Type *etype = atype->getElementType();
    unsigned esize = datalayout->getTypeStoreSize(etype);
    unsigned eoffset = 0;
    for (unsigned idx = 0, end = atype->getArrayNumElements(); idx != end; ++idx) {
      compareObjectStates(os1, offset1 + eoffset, state1, os2, offset2 + eoffset, state2, etype);
      eoffset += esize;
    }

  } else if (type->isFunctionTy()) {
    auto *ftype = cast<FunctionType>(type);
    (void)ftype;
    assert("function type should never occur here");
  }

}

void StateComparator::compareMemoryObjects(const MemoryObject *mo1, uint64_t offset1, ExecutionState *state1,
                                           const MemoryObject *mo2, uint64_t offset2, ExecutionState *state2,
                                           llvm::Type *type) {

  if (!type->isVoidTy()) {
    const ObjectState *os1 = state1->addressSpace.findObject(mo1);
    const ObjectState *os2 = state2->addressSpace.findObject(mo2);
    if (os1 == nullptr || os2 == nullptr) {
      diffs.emplace_back("different: unable to find object an state");
    } else {
      compareObjectStates(os1, offset1, state1, os2, offset2, state2, type);
    }
  }
}

void StateComparator::compareExprs(const ref<ConstantExpr> &expr1, ExecutionState *state1,
                                   const ref<ConstantExpr> &expr2, ExecutionState *state2,
                                   llvm::Type *type) {

  if (!type->isVoidTy()) {
    if (type->isSingleValueType()) {
      if (type->isPointerTy()) {

        // pointer comparison
        comparePtrs(expr1, state1, expr2, state2, cast<PointerType>(type));
      } else {

        // these are supposed to fit in a single register
        // since this is not a pointer value, they can be directly compared
        Expr::Width width = expr1->getWidth();
        if (expr2->getWidth() != width) {
          diffs.emplace_back("difference in expression width");
        } else {
          // most of these types are no more than 64 bits.
          if (width <= Expr::Int64) {
            if (expr1->getZExtValue() != expr2->getZExtValue()) {
              diffs.emplace_back("difference in expression value");
            }
          } else {
            // this is a real hack to deal with bit-long expressions
            long double val1, val2;
            expr1->toMemory(&val1);
            expr2->toMemory(&val2);
            if (val1 != val2) {
              diffs.emplace_back("difference in expression value");
            }
          }
        }
      }
    } else {
      assert("multi-value types should not occur as expressions");
    }
  }
}

void StateComparator::comparePtrs(const ref<klee::ConstantExpr> &expr1, ExecutionState *state1,
                                  const ref<klee::ConstantExpr> &expr2, ExecutionState *state2,
                                  PointerType *type) {

  // do not recurse through the same pointer pair twice, prevents pointer cycles from looping forever
  uint64_t addr1 = expr1->getZExtValue();
  uint64_t addr2 = expr2->getZExtValue();
  auto result = visited_ptrs.insert(make_pair(addr1, addr2));
  if (result.second) {

    // pair was inserted, so we have not been here before...
    ObjectPair pr1, pr2;
    if (state1->addressSpace.resolveOne(expr1, pr1) && state2->addressSpace.resolveOne(expr2, pr2)) {
      uint64_t offset1 = addr1 - pr1.first->address;
      uint64_t offset2 = addr2 - pr2.first->address;
      compareObjectStates(pr1.second, offset1, state1, pr2.second, offset2, state2, type->getPointerElementType());
    } else {
      diffs.emplace_back(("unable to find pointed object"));
    }
  }
}

} // end klee namespace
