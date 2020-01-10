

#include <set>
#include <string>
#include "LocalExecutor.h"
#include "SystemModel.h"

using namespace std;
using namespace llvm;

namespace klee {

SystemModel::SystemModel(LocalExecutor *e, const ModelOptions &o) : executor(e), opts(o), ki(nullptr), fn(nullptr) {

  static const vector<handler_descriptor_t> modeled_fns = {
      {"write", &SystemModel::ExecuteWrite},
      {"read", &SystemModel::ExecuteRead},
      {"isatty", &SystemModel::ExecuteIsaTTY},
      {"posix_fadvise", &SystemModel::ExecuteReturn0_32},
      {"getuid", &SystemModel::ExecuteReturn0_32},
      {"geteuid", &SystemModel::ExecuteReturn0_32},
      {"getgid", &SystemModel::ExecuteReturn0_32},
      {"getegid", &SystemModel::ExecuteReturn0_32},
      {"memset", &SystemModel::ExecuteMemset},
      {"lseek64", &SystemModel::ExecuteReturnMinus1_64},
      {"__check_one_fd", &SystemModel::ExecuteNoop}
  };

  static const vector<handler_descriptor_t> output_fns = {
      { "printf", &SystemModel::ExecuteReturn1_32},
      { "fprintf", &SystemModel::ExecuteReturn1_32},
      { "vprintf", &SystemModel::ExecuteReturn1_32},
      { "vfprintf", &SystemModel::ExecuteReturn1_32},
      { "puts", &SystemModel::ExecuteReturn1_32},
      { "fputs", &SystemModel::ExecuteReturn1_32},
      { "fputs_unlocked", &SystemModel::ExecuteReturn1_32},
      { "putchar", &SystemModel::ExecuteReturnFirstArg},
      { "putc", &SystemModel::ExecuteReturnFirstArg},
      { "fputc", &SystemModel::ExecuteReturnFirstArg},
      { "putchar_unlocked", &SystemModel::ExecuteReturnFirstArg},
      { "putc_unlocked", &SystemModel::ExecuteReturnFirstArg},
      { "fputc_unlocked", &SystemModel::ExecuteReturnFirstArg},
      { "perror", &SystemModel::ExecuteNoop}
  };

  KModule *km = e->getKModule();
  Module *module = km->module;
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
      ref<Expr> arg = executor->eval(ki, idx + 1, state).value;
      args.push_back(arg);
    }
    this->ki = ki;
    this->fn = fn;
    bool result = (this->*handler)(state, args, ret);
    this->ki = nullptr;
    this->fn = nullptr;
    return result;
  }
  return false;
}

bool SystemModel::ExecuteWrite(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 3) {

    ref<ConstantExpr> efd = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> eaddr = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    ref<ConstantExpr> ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    if (efd.get() && eaddr.get() && ecount.get()) {
      int fd = efd->getZExtValue(Expr::Int32);
      uint64_t addr = eaddr->getZExtValue();
      uint64_t count = ecount->getZExtValue();
      if (fd == 1 || fd == 2) {
        ObjectPair op;
        LocalExecutor::ResolveResult result = executor->resolveMO(state, eaddr, op);
        if (result == LocalExecutor::ResolveResult::OK) {
          const MemoryObject *mo = op.first;
          const ObjectState *os = op.second;

          size_t offset = addr - mo->address;
          CharacterOutput *bo = fd == 1 ? &state.stdout_capture : &state.stderr_capture;
          bo->emplace_back();
          os->readConcrete(bo->back(), offset, count);
        }
      }
    }
    retExpr = args[2];
  } else {
    retExpr = ConstantExpr::create(0, Expr::Int64);
  }
  return true;
}

bool SystemModel::ExecuteRead(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 3) {

    ref<ConstantExpr> efd = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> eaddr = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
//    ref<ConstantExpr> ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    if (efd.get() && eaddr.get()) {
      int fd = efd->getZExtValue(Expr::Int32);
      if ((fd == 0) && (!state.stdin_closed) && (state.stdin_offset < executor->moStdInBuff->size)) {
        ExecutionState *ns = executor->clone(&state);

        // close state so no further reads will succeed
        state.stdin_closed = true;

        ObjectPair op;
        LocalExecutor::ResolveResult result = executor->resolveMO(*ns, eaddr, op);
        if (result == LocalExecutor::ResolveResult::OK) {
          const MemoryObject *mo = op.first;
          const ObjectState *os = op.second;

          const ObjectState *stdin_os = ns->addressSpace.findObject(executor->moStdInBuff);
          ref<Expr> ch = stdin_os->read8(ns->stdin_offset++);
          ObjectState *wos = ns->addressSpace.getWriteable(mo, os);
          wos->write8(0, ch);
          ref<Expr> one = ConstantExpr::create(1, Expr::Int64);
          executor->bindLocal(ki, *ns, one);
        }
      }
    }
  }
  retExpr = ConstantExpr::create(0, Expr::Int64);
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

bool SystemModel::ExecuteReturn1_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(1, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturnMinus1_64(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(-1, Expr::Int64);
  return true;
}

bool SystemModel::ExecuteReturn0_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(0, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteNoop(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  return true;
}

bool SystemModel::ExecuteReturnFirstArg(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (!args.empty()) {
    retExpr = args[0];
    return true;
  }
  return false;
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
