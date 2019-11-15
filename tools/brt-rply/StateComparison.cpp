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

void ConstructLookup(vector<ObjectPair> &objs, map<string,ObjectPair*> &mp) {

  mp.clear();
  for (auto &obj : objs) {
    assert(!obj.first->name.empty());
    mp.insert(make_pair(obj.first->name, &obj));
  }
}

bool CompareExecutions(CompareState &version1, CompareState &version2) {

  set<MemKind> kinds = { MemKind::global, MemKind::heap, MemKind::param};

  vector<ObjectPair> written_objs1;
  version1.state->addressSpace.getNamedWrittenMemObjs(written_objs1, kinds);
  vector<ObjectPair> written_objs2;
  version2.state->addressSpace.getNamedWrittenMemObjs(written_objs2, kinds);

  map<string,ObjectPair*> lookup_objs1;
  ConstructLookup(written_objs1, lookup_objs1);
  map<string,ObjectPair*> lookup_objs2;
  ConstructLookup(written_objs2, lookup_objs2);



  return true;
}
