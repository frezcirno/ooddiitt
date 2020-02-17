//
// Created by rrutledge on 10/23/19.
//

#include "StateComparison.h"
#include <vector>
#include <boost/filesystem.hpp>

#include "klee/ExecutionState.h"
#include "klee/Internal/System/Memory.h"

#include "llvm/Support/raw_ostream.h"

using namespace klee;
using namespace llvm;
using namespace std;

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

string get_module_name(KModule *km) {

  boost::filesystem::path path(km->module->getModuleIdentifier());
  return path.filename().string();
}

bool CompareExternalExecutions(CompareState &version1, CompareState &version2, deque<string> &diffs) {

  diffs.clear();

  // unpack the versions for easier access
  ExecutionState *state1 = version1.finalState;
  KModule *kmodule1 = version1.kmodule;
  ExecutionState *state2 = version2.finalState;
  KModule *kmodule2 = version2.kmodule;

  string modID1 = get_module_name(kmodule1);
  string modID2 = get_module_name(kmodule2);

  if (state1->status != state2->status) {
    stringstream ss;
    ss << "status: " << modID1 << '=' << to_string(state1->status) << ' ' << modID2 << '=' << to_string(state2->status);
    diffs.push_back(ss.str());
  }

  assert(state1->arguments.size() < 2);
  assert(state2->arguments.size() < 2);

  if (state1->arguments.empty() && !state2->arguments.empty()) {
    ostringstream ss;
    ss << "exit_code: " << modID1 << "=missing " << modID2 << "=extant";
    diffs.push_back(ss.str());
  }
  if (!state1->arguments.empty() && state2->arguments.empty()) {
    ostringstream ss;
    ss << "exit_code: " << modID1 << "=extant " << modID2 << "=missing";
    diffs.push_back(ss.str());
  }
  if (!state1->arguments.empty() && !state2->arguments.empty()) {
    unsigned exit_code1 = cast<klee::ConstantExpr>(state1->arguments[0])->getZExtValue(Expr::Int32);
    unsigned exit_code2 = cast<klee::ConstantExpr>(state2->arguments[0])->getZExtValue(Expr::Int32);
    if (exit_code1 != exit_code2) {
      ostringstream ss;
      ss << "exit_code: " << modID1 << '=' << exit_code1 << ' ' << modID2 << '=' << exit_code2;
      diffs.push_back(ss.str());
    }
  }

  string stdout1 = to_string(state1->stdout_capture);
  string stdout2 = to_string(state2->stdout_capture);

  if (stdout1 != stdout2) {
    diffs.emplace_back("stdout: ");
    ostringstream ss;
    ss << "  " << modID1 << '=' << stdout1.substr(0, 64);
    diffs.push_back(ss.str());
    ss.str(string());
    ss << "  " << modID2 << '=' << stdout2.substr(0, 64);
    diffs.push_back(ss.str());
  }

  string stderr1 = to_string(state1->stderr_capture);
  string stderr2 = to_string(state2->stderr_capture);

  if (stderr1 != stderr2) {
    diffs.emplace_back("stderr: ");
    ostringstream ss;
    ss << "  " << modID1 << '=' << stderr1.substr(0, 64);
    diffs.push_back(ss.str());
    ss.str(string());
    ss << "  " << modID2 << '=' << stderr2.substr(0, 64);
    diffs.push_back(ss.str());
  }

  if ((state1->stdin_buffer.size() != state2->stdin_buffer.size()) || (state1->eof_counter != state2->eof_counter)) {
    diffs.emplace_back("stdin: ");
  }

  return diffs.empty();
}

const Type *get_return_type(const KModule *kmodule, const string &fn_name) {

  if (const Function *fn = kmodule->getFunction(fn_name)) {
    return fn->getReturnType();
  }
  return nullptr;
}

bool CompareInternalExecutions(CompareState &version1, CompareState &version2, deque<string> &diffs) {

  diffs.clear();

  // unpack the versions for easier access
  ExecutionState *state1 = version1.finalState;
  KModule *kmodule1 = version1.kmodule;
  ExecutionState *state2 = version2.finalState;
  KModule *kmodule2 = version2.kmodule;

  string modID1 = get_module_name(kmodule1);
  string modID2 = get_module_name(kmodule2);

  if (state1->status != state2->status) {
    ostringstream ss;
    ss << "status: " << modID1 << '=' << to_string(state1->status) << ' ' << modID2 << '=' << to_string(state2->status);
    diffs.push_back(ss.str());
  }

  assert(state1->arguments.size() < 2);
  assert(state2->arguments.size() < 2);

  if (state1->arguments.empty() && !state2->arguments.empty()) {
    ostringstream ss;
    ss << "return: " << modID1 << "=missing " << modID2 << "=extant";
    diffs.push_back(ss.str());
  }
  if (!state1->arguments.empty() && state2->arguments.empty()) {
    ostringstream ss;
    ss << "return: " << modID1 << "=extant " << modID2 << "=missing";
    diffs.push_back(ss.str());
  }
  if (!state1->arguments.empty() && !state2->arguments.empty()) {

    // get the function return type
    const Type *type1 = get_return_type(kmodule1, state1->name);
    const Type *type2 = get_return_type(kmodule2, state2->name);
    string s1 = to_string(type1);
    string s2 = to_string(type2);
    if (s1 != s2) {
      ostringstream ss;
      ss << "return type: " << modID1 << '=' << s1 << ' ' << modID2 << '=' << s2;
      diffs.push_back(ss.str());
    }
    if (type1->isPointerTy()) {

      // RLR TODO: what about pointers?
      klee::ref<klee::ConstantExpr> ptr1 = cast<klee::ConstantExpr>(state1->arguments[0]);
      klee::ref<klee::ConstantExpr> ptr2 = cast<klee::ConstantExpr>(state2->arguments[0]);
      ObjectPair op1;
      bool b1 = state1->addressSpace.resolveOne(ptr1, op1);
      ObjectPair op2;
      bool b2 = state2->addressSpace.resolveOne(ptr2, op2);
      if (b1 && b2) {
        const ObjectState *os1 = op1.second;
        const ObjectState *os2 = op2.second;

        if (os1->visible_size != os2->visible_size) {
          ostringstream ss;
          ss << "ret ptr'd size: " << modID1 << '=' << os1->visible_size << ' ' << modID2 << "=" << os2->visible_size;
          diffs.push_back(ss.str());
        }

        deque<unsigned> discrepancies;
        for (unsigned idx = 0, end = os1->visible_size; idx < end; ++idx) {
          if (!os1->isByteConcrete(idx) || !os2->isByteConcrete(idx) || os1->readConcrete(idx) != os2->readConcrete(idx)) {
            discrepancies.push_back(idx);
          }
        }
        if (!discrepancies.empty()) {
          ostringstream ss;
          ss << "ret ptr'd values, indices: ";
          bool first = true;
          for (auto idx : discrepancies) {
            if (!first) ss << ',';
            else first=false;
            ss << idx;
          }
          diffs.push_back(ss.str());
        }

      }

    } else if (type1->isSingleValueType()) {
      uint64_t val1 = cast<klee::ConstantExpr>(state1->arguments[0])->getZExtValue();
      uint64_t val2 = cast<klee::ConstantExpr>(state2->arguments[0])->getZExtValue();
      if (val1 != val2) {
        ostringstream ss;
        ss << "return value: " << modID1 << '=' << val1 << ' ' << modID2 << '=' << val2;
        diffs.push_back(ss.str());
      }
    } else {
      // RLR TODO: no idea what to do now...
    }
  }

  // RLR TODO: look at global, heap, etc. state
  static set<MemKind> kinds = { MemKind::global, MemKind::param, MemKind::lazy};

  map<string,ObjectPair> written_objs1;
  state1->addressSpace.getNamedWrittenMemObjs(written_objs1, kinds);
  map<string,ObjectPair> written_objs2;
  state2->addressSpace.getNamedWrittenMemObjs(written_objs2, kinds);

  for (const auto &pr : written_objs1) {
    string name = pr.first;
    const MemoryObject *mo1 = pr.second.first;
    if (!mo1->type->isPointerTy()) {
      const ObjectState *os1 = pr.second.second;
      auto itr = written_objs2.find(name);
      if (itr == written_objs2.end()) {
        ostringstream ss;
        ss << "value written: " << modID1 << '=' << name << ' ' << modID2 << "=";
        diffs.push_back(ss.str());
      } else {
        const MemoryObject *mo2 = itr->second.first;
        const ObjectState *os2 = itr->second.second;

        if (os1->visible_size != os2->visible_size) {
          ostringstream ss;
          ss << "var size: " << name << ", " << modID1 << '=' << os1->visible_size << ' ' << modID2 << "=" << os2->visible_size;
          diffs.push_back(ss.str());
        }

        deque<unsigned> discrepancies;
        for (unsigned idx = 0, end = os1->visible_size; idx < end; ++idx) {
          if (os1->isByteWritten(idx) || os2->isByteWritten(idx)) {
            if (!os1->isByteConcrete(idx) || !os2->isByteConcrete(idx) || os1->readConcrete(idx) != os2->readConcrete(idx)) {
              discrepancies.push_back(idx);
            }
          }
        }
        if (!discrepancies.empty()) {
          ostringstream ss;
          ss << "var values: " << name << ", indices: ";
          bool first = true;
          for (auto idx : discrepancies) {
            if (!first) ss << ',';
            else first=false;
            ss << idx;
          }
          diffs.push_back(ss.str());
        }
      }
    }
  }

  string stdout1 = to_string(state1->stdout_capture);
  string stdout2 = to_string(state2->stdout_capture);

  if (stdout1 != stdout2) {
    diffs.emplace_back("stdout: ");
    ostringstream ss;
    ss << "  " << modID1 << '=' << stdout1.substr(0, 64);
    diffs.push_back(ss.str());
    ss.str(string());
    ss << "  " << modID2 << '=' << stdout2.substr(0, 64);
    diffs.push_back(ss.str());
  }

  string stderr1 = to_string(state1->stderr_capture);
  string stderr2 = to_string(state2->stderr_capture);

  if (stderr1 != stderr2) {
    diffs.emplace_back("stderr: ");
    ostringstream ss;
    ss << "  " << modID1 << '=' << stderr1.substr(0, 64);
    diffs.push_back(ss.str());
    ss.str(string());
    ss << "  " << modID2 << '=' << stderr2.substr(0, 64);
    diffs.push_back(ss.str());
  }

  return diffs.empty();
}

CompareState::~CompareState() {
  // module is deleted with module_cache

//  delete initialState;
//  delete finalState;
// baaaaad idea... deleted with address space
}

#if 0 == 1


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

#endif

