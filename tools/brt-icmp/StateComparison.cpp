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
using namespace klee;
using namespace std;

bool CompareOutput(const CharacterOutput &out1, const CharacterOutput &out2) {

  vector<unsigned char> output1;
  vector<unsigned char> output2;
  out1.get_data(output1);
  out2.get_data(output2);
  return output1 == output2;
}

string get_module_name(KModule *km) {

  boost::filesystem::path path(km->module->getModuleIdentifier());
  return path.filename().string();
}

bool CompareExecutions(CompareState &version1, CompareState &version2, bool extern_only) {

  // unpack the versions for easier access
  ExecutionState *state1 = version1.state;
  KModule *kmodule1 = version1.kmodule;
  ExecutionState *state2 = version2.state;
  KModule *kmodule2 = version2.kmodule;

  boost::filesystem::path path1(kmodule1->module->getModuleIdentifier());
  boost::filesystem::path path2(kmodule2->module->getModuleIdentifier());

  string modID1 = get_module_name(kmodule1);
  string modID2 = get_module_name(kmodule2);

  if (state1->status != state2->status) {
    outs() << "diff status: " << modID1 << '=' << to_string(state1->status) << ' ' << modID2 << '=' << to_string(state2->status);
    return false;
  }

  if (extern_only) {
    assert(state1->arguments.size() < 2);
    assert(state2->arguments.size() < 2);
    if (state1->arguments.empty() || state2->arguments.empty()) {
      outs() << modID1 << " or " << modID2 << " did not return a value";
      return false;
    }
    unsigned exit_code1 = cast<ConstantExpr>(state1->arguments[0])->getZExtValue(Expr::Int32);
    unsigned exit_code2 = cast<ConstantExpr>(state2->arguments[0])->getZExtValue(Expr::Int32);
    if (exit_code1 != exit_code2) {
      outs() << "diff exit_code: " << modID1 << '=' << exit_code1 << ' ' << modID2 << '=' << exit_code2;
      return false;
    }

    if (!CompareOutput(state1->stdout_capture, state2->stdout_capture)) {
      outs() << "diff stdout";
      return false;
    }

    if (!CompareOutput(state1->stderr_capture, state2->stderr_capture)) {
      outs() << "diff stderr";
      return false;
    }
  } else {

    // need to check internal state


  }

#if 0 == 1
  vector<unsigned char> stdout1;
  version1.state->stdout_capture.get_data(stdout1);
//  vector<unsigned char> stderr1;
//  version1.state->stderr_capture.get_data(stderr1);

  vector<unsigned char> stdout2;
  version2.state->stdout_capture.get_data(stdout2);
//  vector<unsigned char> stderr2;
//  version2.state->stderr_capture.get_data(stderr2);

  if (stdout1 != stdout2) {
    outs() << "stdout differs";
    return false;
  }

  if (version1.state->status != version2.state->status) {
    outs() << "different completion status";
    return false;
  }

  assert(version1.state->arguments.size() <= 1 && version2.state->arguments.size() <= 1);
  if (version1.state->arguments.size() != version2.state->arguments.size()) {
    outs() << "different number of outputs";
    return false;
  }

  for (unsigned idx = 0, end = version1.state->arguments.size(); idx != end; ++idx) {
    klee::ref<ConstantExpr> arg1 = dyn_cast<ConstantExpr>(version1.state->arguments[idx]);
    klee::ref<ConstantExpr> arg2 = dyn_cast<ConstantExpr>(version2.state->arguments[idx]);
    assert(!arg1.isNull() && !arg2.isNull());
    if (arg1->getWidth() != arg2->getWidth()) {
      outs() << "different return width";
      return false;
    } else if (arg1->getZExtValue() != arg2->getZExtValue()) {
      outs() << "different return value";
      return false;
    }
  }

//  static set<MemKind> kinds = { MemKind::global, MemKind::heap, MemKind::param, MemKind::lazy};
  static set<MemKind> kinds = { MemKind::global, MemKind::param, MemKind::lazy};

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
      outs() << "written variable \'" << name << "\' not found in " << modID2;
      return false;
    } else {
      const MemoryObject *mo2 = itr->second.first;
      const ObjectState *os2 = itr->second.second;

      if (os1->visible_size != os2->visible_size) {
        outs() << "written variable \'" << name << "\' has different size in " << modID2;
        return false;
      }

      for (unsigned idx = 0, end = os1->visible_size; idx < end; ++idx) {

        if (os1->isByteWritten(idx) || os2->isByteWritten(idx)) {
          if (!os1->isByteConcrete(idx) || !os2->isByteConcrete(idx) || os1->readConcrete(idx) != os2->readConcrete(idx)) {
            outs() << "variable \'" << name << "\' different at offset " << idx;
            return false;
          }
        }
      }
    }
  }

//  vector<unsigned char> stdout1;
//  version1.state->stdout_capture.get_data(stdout1);
//  vector<unsigned char> stderr1;
//  version1.state->stderr_capture.get_data(stderr1);
//
//  vector<unsigned char> stdout2;
//  version2.state->stdout_capture.get_data(stdout2);
//  vector<unsigned char> stderr2;
//  version2.state->stderr_capture.get_data(stderr2);

//  if (stdout1 != stdout2) {
//    outs() << "stdout differs";
//    return false;
//  }
#endif
  return true;
}
