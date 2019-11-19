

#include <set>
#include <string>
#include "LocalExecutor.h"
#include "SystemModel.h"

using namespace std;
using namespace llvm;

namespace klee {

SystemModel::SystemModel(LocalExecutor *e, const ModelOptions &o) : executor(e), opts(o) {

  static const vector<handler_descriptor_t> modeled_fns = {
      {"write", &SystemModel::ExecuteWrite},
      {"isatty", &SystemModel::ExecuteIsaTTY},
      {"posix_fadvise", &SystemModel::ExecuteReturn0},
      {"getuid", &SystemModel::ExecuteReturn0},
      {"geteuid", &SystemModel::ExecuteReturn0},
      {"getgid", &SystemModel::ExecuteReturn0},
      {"getegid", &SystemModel::ExecuteReturn0},
      {"memset", &SystemModel::ExecuteMemset}
  };

  static const vector<handler_descriptor_t> output_fns = {
      { "printf", &SystemModel::ExecuteReturn1},
      { "fprintf", &SystemModel::ExecuteReturn1},
      { "vprintf", &SystemModel::ExecuteReturn1},
      { "vfprintf", &SystemModel::ExecuteReturn1},
      { "puts", &SystemModel::ExecuteReturn1},
      { "fputs", &SystemModel::ExecuteReturn1},
      { "fputs_unlocked", &SystemModel::ExecuteReturn1},
      { "putchar", &SystemModel::ExecuteReturnFirstArg},
      { "putc", &SystemModel::ExecuteReturnFirstArg},
      { "fputc", &SystemModel::ExecuteReturnFirstArg},
      { "putchar_unlocked", &SystemModel::ExecuteReturnFirstArg},
      { "putc_unlocked", &SystemModel::ExecuteReturnFirstArg},
      { "fputc_unlocked", &SystemModel::ExecuteReturnFirstArg},
      { "perror", &SystemModel::ExecuteNoop}
  };

  Module *module = executor->getKModule()->module;
  for (const auto &pr : modeled_fns) {
    if (Function *fn = module->getFunction(pr.first)) {
      modeled_names.insert(pr.first);
      dispatch[fn] = pr.second;
    }
  }
  if (opts.doModelStdOutput) {
    for (const auto &pr : output_fns) {
      if (Function *fn = module->getFunction(pr.first)) {
        modeled_names.insert(pr.first);
        dispatch[fn] = pr.second;
      }
    }
  }
}

void SystemModel::GetModeledExternals(set<string> &names) const {

  names.insert(modeled_names.begin(), modeled_names.end());
}

bool SystemModel::ShouldBeModeled(const std::string &name) const {

  static set<string> desired = { "memcpy", "memmove", "memcmp", "strlen" };
  auto itr = desired.find(name);
  return itr != desired.end();
}

bool SystemModel::Execute(ExecutionState &state, Function *fn, KInstruction *ki, const CallSite &cs, ref<Expr> &ret) {

  auto itr = dispatch.find(fn);
  if (itr != dispatch.end()) {
    handler_t SystemModel::*handler = itr->second;

    // create a vector of arguments
    unsigned num_args = cs.arg_size();
    vector<ref<Expr> > args;
    args.reserve(num_args);
    for (unsigned idx = 0; idx < num_args; ++idx) {
      ref<Expr> arg = executor->eval(ki, idx+1, state).value;
      args.push_back(arg);
    }
    return (this->*handler)(state, args, ret);
  }
  return false;
}

bool SystemModel::ExecuteWrite(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 3) {
    retExpr = args[2];
  } else {
    return ExecuteReturn0(state, args, retExpr);
  }
  return true;
}

bool SystemModel::ExecuteIsaTTY(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  unsigned result = 0;
  if (!args.empty()) {
    ref<Expr> fd = args[0];
    if (isa<ConstantExpr>(fd)) {
      ref<ConstantExpr> cfd = cast<ConstantExpr>(fd);
      unsigned desc = cfd->getZExtValue(Expr::Int32);
      if (desc < 3)
        result = 1;
    }
  }
  retExpr = ConstantExpr::create(result, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturn1(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(1, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturn0(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(0, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteNoop(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  return true;
}

bool SystemModel::ExecuteReturnFirstArg(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (!args.empty()) {
    retExpr = args[0];
  } else {
    return ExecuteReturn0(state, args, retExpr);
  }
  return true;
}

bool SystemModel::ExecuteMemset(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 3) {
    ref<Expr> addr = executor->toUnique(state, args[0]);
    ref<Expr> val = ExtractExpr::create(args[1], 0, Expr::Int8);
    val = executor->toUnique(state, val);
    ref<Expr> count = executor->toUnique(state, args[2]);
    if ((isa<ConstantExpr>(addr) && isa<ConstantExpr>(count))) {

      ObjectPair op;
      LocalExecutor::ResolveResult result = executor->resolveMO(state, addr, op);
      if (result == LocalExecutor::ResolveResult::OK) {
        const MemoryObject *mo = op.first;
        const ObjectState *os = op.second;

        uint64_t caddr = cast<ConstantExpr>(addr)->getZExtValue(Expr::Int64);
        uint64_t ccount = cast<ConstantExpr>(count)->getZExtValue(Expr::Int64);
        uint64_t offset = caddr - mo->address;
        if (offset + ccount < mo->address + mo->size) {
          ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          while (ccount-- > 0) {
            wos->write8(offset++, val);
          }
        }
      }
      retExpr = addr;
      return true;
    }
    return false;
  }
  retExpr = ConstantExpr::createPointer(0);
  return true;
}

// RLR TODO: other functions to model: memcpy, memcmp, memmove, strlen, strcpy,

}
