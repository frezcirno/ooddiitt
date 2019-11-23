//
// Created by rrutledge on 10/23/19.
//

#include "StateComparison.h"
#include <vector>

#include "klee/ExecutionState.h"
#include "klee/Internal/System/Memory.h"

#include "llvm/Support/raw_ostream.h"


using namespace llvm;
using namespace klee;
using namespace std;

bool CompareExecutions(CompareState &version1, CompareState &version2) {

  string modID1 = version1.kmodule->module->getModuleIdentifier();
  string modID2 = version2.kmodule->module->getModuleIdentifier();

  if (version1.state->status != version2.state->status) {
    outs() << "different completion status\n";
    return false;
  }

  assert(version1.state->arguments.size() <= 1 && version2.state->arguments.size() <= 1);
  if (version1.state->arguments.size() != version2.state->arguments.size()) {
    outs() << "different number of outputs\n";
    return false;
  }

  for (unsigned idx = 0, end = version1.state->arguments.size(); idx != end; ++idx) {
    klee::ref<ConstantExpr> arg1 = dyn_cast<ConstantExpr>(version1.state->arguments[idx]);
    klee::ref<ConstantExpr> arg2 = dyn_cast<ConstantExpr>(version2.state->arguments[idx]);
    assert(!arg1.isNull() && !arg2.isNull());
    if (arg1->getWidth() != arg2->getWidth()) {
      outs() << "different return width\n";
      return false;
    } else if (arg1->getZExtValue() != arg2->getZExtValue()) {
      outs() << "different return value" << '\n';
      return false;
    }
  }

  static set<MemKind> kinds = { MemKind::global, MemKind::heap, MemKind::param, MemKind::lazy};

  map<string,ObjectPair> written_objs1;
  map<string,ObjectPair> written_objs2;

  version1.state->addressSpace.getNamedWrittenMemObjs(written_objs1, kinds);
  version2.state->addressSpace.getNamedWrittenMemObjs(written_objs2, kinds);

  for (const auto &pr : written_objs1) {
    string name = pr.first;
    const MemoryObject *mo1 = pr.second.first;
    const ObjectState *os1 = pr.second.second;

    auto itr = written_objs2.find(name);
    if (itr == written_objs2.end()) {
      outs() << "written variable \'" << name << "\' not found in " << modID2 << '\n';
      return false;
    } else {
      const MemoryObject *mo2 = itr->second.first;
      const ObjectState *os2 = itr->second.second;

      if (os1->visible_size != os2->visible_size) {
        outs() << "written variable \'" << name << "\' has different size in " << modID2 << '\n';
        return false;
      }

      for (unsigned idx = 0, end = os1->visible_size; idx < end; ++idx) {

        if (os1->isByteWritten(idx) || os2->isByteWritten(idx)) {
          if (!os1->isByteConcrete(idx) || !os2->isByteConcrete(idx) || os1->readConcrete(idx) != os2->readConcrete(idx)) {
            outs() << "variable \'" << name << "\' different at offset " << idx << '\n';
            return false;
          }
        }
      }
    }
  }
  return true;
}
