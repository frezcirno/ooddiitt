

#include <set>
#include <string>
#include "LocalExecutor.h"
#include "SystemModel.h"

using namespace std;
using namespace llvm;

namespace klee {

const vector<SystemModel::handler_descriptor_t> SystemModel::modeled_fns = {
    {"write", &SystemModel::ExecuteWrite},
    {"read", &SystemModel::ExecuteRead},
    {"isatty", &SystemModel::ExecuteIsaTTY},
    {"posix_fadvise", &SystemModel::ExecuteReturn0_32},
    {"is_selinux_enabled", &SystemModel::ExecuteReturn0_32},
    {"kill", &SystemModel::ExecuteReturn0_32},
    {"nanosleep", &SystemModel::ExecuteReturn0_32},
    {"getpid", &SystemModel::ExecuteReturn42_32},
    {"getuid", &SystemModel::ExecuteReturn0_32},
    {"geteuid", &SystemModel::ExecuteReturn0_32},
    {"getgid", &SystemModel::ExecuteReturn0_32},
    {"getegid", &SystemModel::ExecuteReturn0_32},
    {"memset", &SystemModel::ExecuteMemset},
    {"lseek64", &SystemModel::ExecuteReturnMinus1_64},
    {"lseek", &SystemModel::ExecuteReturnMinus1_64},
    {"open", &SystemModel::ExecuteReturnMinus1_32},
    {"openat", &SystemModel::ExecuteReturnMinus1_32},
    {"close", &SystemModel::ExecuteReturn0_32},
    {"fcntl", &SystemModel::ExecuteReturnMinus1_32},
    {"floor", &SystemModel::ExecuteFloor},
    {"rint", &SystemModel::ExecuteRint},
    {"fabs", &SystemModel::ExecuteFabs},
    {"modf", &SystemModel::ExecuteModf},
    {"__check_one_fd", &SystemModel::ExecuteNoop}
};

const vector<SystemModel::handler_descriptor_t> SystemModel::output_fns = {
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


SystemModel::SystemModel(LocalExecutor *e, const ModelOptions &o) : executor(e), opts(o), ki(nullptr), fn(nullptr) {

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

// static
void SystemModel::filterHandledFunctions(std::set<const llvm::Value*> &fns) {

  // gather a list of functions handled here
  std::set<std::string> names;
  for (const auto &handler : modeled_fns) {
    names.insert(handler.first);
  }
  for (const auto &handler : output_fns) {
    names.insert(handler.first);
  }

  // remove functions defined here
  auto itr = fns.begin(), end = fns.end();
  while (itr != end) {
    const llvm::Value *val = *itr;
    const auto fn = dyn_cast<const llvm::Function>(val);
    if (fn != nullptr && fn->hasName() && names.count(fn->getName().str())) {
      itr = fns.erase(itr);
    } else {
      ++itr;
    }
  }
}

// static
void SystemModel::filterHandledGlobals(std::set<const llvm::Value*> &gbs) {

  // none
}

void SystemModel::GetModeledExternals(set<string> &names) const {

  names.insert(modeled_names.begin(), modeled_names.end());
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
          vector<unsigned char> write;
          os->readConcrete(write, offset, count);
          bo->emplace_back(write);
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

  unsigned ret = 0;
  if (args.size() == 3) {

    ref<ConstantExpr> efd = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> eaddr = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
//    ref<ConstantExpr> ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    if (efd.get() && eaddr.get()) {
      int fd = efd->getZExtValue(Expr::Int32);
      if (fd == 0) {
        if (executor->moStdInBuff != nullptr) {
          // if not null then we are generating symbolic inputs
          if ((!state.stdin_closed) && (state.stdin_offset < executor->moStdInBuff->size)) {
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
              unsigned offset = eaddr->getZExtValue() - mo->address;
              wos->write8(offset, ch);
              ref<Expr> one = ConstantExpr::create(1, Expr::Int64);
              executor->bindLocal(ki, *ns, one);
            }
          }
        } else {
          // since moStdInBuff is null, then we are replaying previous data

          if (!state.stdin_buffer.empty()) {

            // pop off a character to return
            unsigned char ch = state.stdin_buffer.back();
            state.stdin_buffer.pop_back();

            ObjectPair op;
            LocalExecutor::ResolveResult result = executor->resolveMO(state, eaddr, op);
            if (result == LocalExecutor::ResolveResult::OK) {
              const MemoryObject *mo = op.first;
              const ObjectState *os = op.second;

              ObjectState *wos = state.addressSpace.getWriteable(mo, os);
              unsigned offset = eaddr->getZExtValue() - mo->address;
              wos->write8(offset, ch);
              ret = 1;
            }
          } else {
            state.eof_counter += 1;
          }
        }
      }
    }
  }
  retExpr = ConstantExpr::create(ret, Expr::Int64);
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

bool SystemModel::ExecuteReturn0_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(0, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturn42_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(42, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturnMinus1_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  uint64_t val = (uint32_t) -1;
  retExpr = ConstantExpr::create(val, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturnMinus1_64(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(-1, Expr::Int64);
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
    ref<Expr> addr = executor->ensureUnique(state, args[0]);
    ref<Expr> val = ExtractExpr::create(args[1], 0, Expr::Int8);
    val = executor->toUnique(state, val);
    ref<Expr> count = executor->ensureUnique(state, args[2]);
    if ((isa<ConstantExpr>(addr) && isa<ConstantExpr>(count))) {

      ObjectPair op;
      LocalExecutor::ResolveResult result = executor->resolveMO(state, addr, op);
      if (result == LocalExecutor::ResolveResult::OK) {
        const MemoryObject *mo = op.first;
        const ObjectState *os = op.second;

        uint64_t caddr = cast<ConstantExpr>(addr)->getZExtValue(Expr::Int64);
        uint64_t ccount = cast<ConstantExpr>(count)->getZExtValue(Expr::Int64);
        uint64_t offset = caddr - mo->address;
        if (offset + ccount <= mo->size) {
          ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          while (ccount-- > 0) {
            wos->write8(offset++, val);
          }
        } else {
          // copy out-of-bounds
          executor->terminateState(state, "out-of-bounds memset");
          return true;
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

static inline const fltSemantics * fpWidthToSemantics(unsigned width) {
  switch(width) {
  case Expr::Int32:
    return &APFloat::IEEEsingle;
  case Expr::Int64:
    return &APFloat::IEEEdouble;
  case Expr::Fl80:
    return &APFloat::x87DoubleExtended;
  default:
    return 0;
  }
}

bool SystemModel::ExecuteFloor(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 1) {
    ref<ConstantExpr> val = executor->toConstant(state, args[0], "floor()");
    APFloat result(*fpWidthToSemantics(val->getWidth()), val->getAPValue());
    result.roundToIntegral(APFloat::rmTowardNegative);
    retExpr = ConstantExpr::alloc(result.bitcastToAPInt());
    return true;
  }
  return false;
}

bool SystemModel::ExecuteRint(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 1) {
    ref<ConstantExpr> val = executor->toConstant(state, args[0], "rint()");
    APFloat result(*fpWidthToSemantics(val->getWidth()), val->getAPValue());
    result.roundToIntegral(APFloat::rmNearestTiesToAway);
    retExpr = ConstantExpr::alloc(result.bitcastToAPInt());
    return true;
  }
  return false;
}

bool SystemModel::ExecuteFabs(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 1) {
    ref<ConstantExpr> val = executor->toConstant(state, args[0], "fabs()");
    APFloat result(*fpWidthToSemantics(val->getWidth()), val->getAPValue());
    result.clearSign();
    retExpr = ConstantExpr::alloc(result.bitcastToAPInt());
    return true;
  }
  return false;
}

bool SystemModel::ExecuteModf(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 2) {
    ref<ConstantExpr> val = executor->toConstant(state, args[0], "modf()");
    ref<ConstantExpr> ptr = executor->toConstant(state, args[1], "modf()");
    APFloat result(*fpWidthToSemantics(val->getWidth()), val->getAPValue());
    APFloat integer = result;
    APFloat fraction = result;
    double i_test1 = integer.convertToDouble();
    double f_test1 = fraction.convertToDouble();
    integer.roundToIntegral(APFloat::rmTowardZero);
    fraction.subtract(integer, APFloat::rmTowardPositive);
    ref<ConstantExpr> outparam = ConstantExpr::alloc(integer.bitcastToAPInt());

    double i_test2 = integer.convertToDouble();
    double f_test2 = fraction.convertToDouble();

    ObjectPair op;
    LocalExecutor::ResolveResult res = executor->resolveMO(state, ptr, op);
    if (res == LocalExecutor::ResolveResult::OK) {
      const MemoryObject *mo = op.first;
      const ObjectState *os = op.second;
      ObjectState *wos = state.addressSpace.getWriteable(mo, os);
      ref<Expr> offset = mo->getOffsetExpr(ptr);
      wos->write(offset, outparam);
    }
    retExpr = ConstantExpr::alloc(fraction.bitcastToAPInt());
    return true;
  }
  return false;
}



// RLR TODO: other functions to model: memcpy, memcmp, memmove, strlen, strcpy,

}
