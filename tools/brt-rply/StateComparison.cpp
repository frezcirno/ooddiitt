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

  if (version1.state->status != version2.state->status) {
    outs() << "different completion status\n";
    return false;
  }

  if (version1.state->arguments.size() != version2.state->arguments.size()) {
    outs() << "different number of outputs\n";
    return false;
  }

  for (unsigned idx = 0, end = version1.state->arguments.size(); idx != end; ++idx) {
    if (version1.state->arguments[idx] != version2.state->arguments[idx]) {
      outs() << "different output value at index " << idx << '\n';
      return false;
    }
  }

  static set<MemKind> kinds = { MemKind::global, MemKind::heap, MemKind::param};

  map<string,ObjectPair> written_objs1;
  version1.state->addressSpace.getNamedWrittenMemObjs(written_objs1, kinds);
  string modID1 = version1.kmodule->module->getModuleIdentifier();
  string modID2 = version2.kmodule->module->getModuleIdentifier();

  map<string,ObjectPair> written_objs2;
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
        if (!os1->isByteConcrete(idx)) {
          outs() << "written variable \'" << name << "\' is not concrete in " << modID1 << " at offset " << idx << '\n';
          return false;
        }
        if (!os2->isByteConcrete(idx)) {
          outs() << "written variable \'" << name << "\' is not concrete in " << modID2 << " at offset " << idx << '\n';
          return false;
        }
        if (os1->readConcrete(idx) != os2->readConcrete(idx)) {
          outs() << "written variable \'" << name << "\' differs in " << modID2 << " at offset " << idx << '\n';
          return false;
        }
      }
    }
  }
  return true;
}
