

#include <set>
#include <string>
#include "LocalExecutor.h"
#include "TimingSolver.h"
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
    {"setlocale", &SystemModel::ExecuteReturnNull},
    {"bindtextdomain", &SystemModel::ExecuteReturnNull},
    {"textdomain", &SystemModel::ExecuteReturnNull},
    {"__o_assert_fail", &SystemModel::ExecuteOAssertFail},
//    {"xstrtod", &SystemModel::ExecuteXStrToD},
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


const ref<ConstantExpr> SystemModel::expr_true = ConstantExpr::create(1, Expr::Bool);
const ref<ConstantExpr> SystemModel::expr_false = ConstantExpr::create(0, Expr::Bool);

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
            if (ns != nullptr) {

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
                if (ki) {
                  executor->frequent_forkers[ki->info->assemblyLine] += 1;
                }
              }
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

bool SystemModel::ExecuteReturnNull(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::createPointer(0);
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
          executor->terminateStateOnMemFault(state, this->ki, addr, mo, "out-of-bounds memset");
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
    integer.roundToIntegral(APFloat::rmTowardZero);
    fraction.subtract(integer, APFloat::rmTowardPositive);
    ref<ConstantExpr> outparam = ConstantExpr::alloc(integer.bitcastToAPInt());

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

bool SystemModel::ExecuteOAssertFail(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  unsigned id = 0;
  if (!args.empty()) {
    ref<ConstantExpr> id_expr = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    if (!id_expr.isNull()) {
      id = id_expr->getZExtValue();
    }
  }
  state.o_asserts.emplace_back(id, ki);
  return true;
}


bool SystemModel::canConstrainString(ExecutionState &state, const ObjectState *os, unsigned index, const string &str) {

  // check each character of string
  for (char ch : str) {
    ref<Expr> ch1 = os->read8(index);
    ref<Expr> ch2 = ConstantExpr::create(ch, ch1->getWidth());
    if (executor->solver->mustBeFalse(state, EqExpr::create(ch1, ch2))) {
      return false;
    }
    index += 1;
  }
  // finally, check for null termination
  ref<Expr> ch1 = os->read8(index);
  ref<Expr> ch2 = ConstantExpr::create(0, ch1->getWidth());
  return (!executor->solver->mustBeFalse(state, EqExpr::create(ch1, ch2)));
}

bool SystemModel::doConstrainString(ExecutionState &state, const ObjectState *os, unsigned index, const string &str) {

  if (canConstrainString(state, os, index, str)) {

    // constrain each character of string
    for (char ch : str) {
      ref<Expr> ch1 = os->read8(index);
      ref<Expr> ch2 = ConstantExpr::create(ch, ch1->getWidth());
      executor->addConstraint(state, EqExpr::create(ch1, ch2));
      index += 1;
    }
    // finally, add null termination
    ref<Expr> ch1 = os->read8(index);
    ref<Expr> ch2 = ConstantExpr::create(0, ch1->getWidth());
    executor->addConstraint(state, EqExpr::create(ch1, ch2));
    return true;
  }
  return false;
}

bool SystemModel::ExecuteXStrToD(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  ref<ConstantExpr> str = executor->toConstant(state, args[0], "XStrToD");
  ref<ConstantExpr> ptr = executor->toConstant(state, args[2], "XStrToD");

  ObjectPair op;
  if (executor->resolveMO(state, str, op) == LocalExecutor::ResolveResult::OK) {

    ref<Expr> ch = op.second->read8(0);
    if (!executor->isUnique(state, ch)) {
      if (doConstrainString(state, op.second, 0, "1")) {
        state.restartInstruction();
        ostringstream ss;
        ss << "xstrtod: " << op.first->name << " constrained";
        state.messages.push_back(ss.str());
        outs () << ss.str() << oendl;
        return true;
      } else {
        ostringstream ss;
        ss << "xstrtod: " << op.first->name << " failed to constrain";
        state.messages.push_back(ss.str());
        outs () << ss.str() << oendl;
      }
    } else {
      ref<ConstantExpr> value;
      executor->solver->getValue(state, ch, value);
      char c = value->getZExtValue(8);
      ostringstream ss;
      ss << "xstrtod: " << op.first->name << " \'" << c << "\' is unique";
      state.messages.push_back(ss.str());
      outs () << ss.str() << oendl;
    }
  }

#if 0 == 1

//  static vector<string> values = { "0.0", "-3.0" , "-2.0" , "-1.0" , "-0.5", "-0.1", "0.1" , "0.5", "1.0" , "2.0" , "3.0" };
  static vector<string> values = { "0", "1", "2" };

  if (executor->getOptions().mode == ExecModeID::igen) {

    // in input generation mode
    ObjectPair op;
    if (executor->resolveMO(state, str, op) == LocalExecutor::ResolveResult::OK) {
      ref<Expr> ch = op.second->read8(0);
      if (!executor->isUnique(state, ch)) {

        for (auto itr = values.begin(), end = values.end(); itr != end; ++itr) {
          // skip the first
          if (itr != values.begin()) {

            ExecutionState *ns = executor->clone(&state);
            if (ns != nullptr) {
              ObjectPair op2;
              if (executor->resolveMO(*ns, str, op2) == LocalExecutor::ResolveResult::OK) {
                if (doConstrainString(*ns, op2.second, 0, *itr)) {
                  if (ki) {
                    executor->frequent_forkers[ki->info->assemblyLine] += 1;
                  }
                  ns->restartInstruction();
                } else {
                  executor->terminateStateOnDispose(*ns, "unsatisfiable xstrtod");
                }
              }
            }
          }
        }
        if (doConstrainString(state, op.second, 0, values.front())) {
          state.restartInstruction();
          return true;
        }
      }
    }
  }
#endif
  return false;
}

#if 0 == 1
bool SystemModel::ExecuteXStrToD(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  static vector<double> values = { -3.0 , -2.0 , -1.0 , -0.5, -0.1, 0.1 , 0.5, 1.0 , 2.0 , 3.0 };
  ref<ConstantExpr> str = executor->toConstant(state, args[0], "XStrToD");
  ref<ConstantExpr> ptr = executor->toConstant(state, args[2], "XStrToD");
  unsigned result = 0;

  if (executor->getOptions().mode == ExecModeID::igen) {

    // in input generation mode
    ObjectPair op;
    LocalExecutor::ResolveResult res = executor->resolveMO(state, str, op);
    if (state.isSymbolic(op.first)) {

      for (auto value : values) {

        ExecutionState *ns = executor->clone(&state);
        res = executor->resolveMO(*ns, ptr, op);
        if (res == LocalExecutor::ResolveResult::OK) {
          const MemoryObject *mo = op.first;
          const ObjectState *os = op.second;
          ObjectState *wos = ns->addressSpace.getWriteable(mo, os);
          ref<Expr> offset = mo->getOffsetExpr(ptr);

          llvm::APFloat f(value);
          ref<ConstantExpr> outparam = ConstantExpr::alloc(f.bitcastToAPInt());
          wos->write(offset, outparam);
          ns->fps_produced.push_back(value);
          executor->bindLocal(ki, *ns, expr_true);
        }
      }

      res = executor->resolveMO(state, ptr, op);
      if (res == LocalExecutor::ResolveResult::OK) {
        const MemoryObject *mo = op.first;
        const ObjectState *os = op.second;
        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
        ref<Expr> offset = mo->getOffsetExpr(ptr);

        llvm::APFloat f(0.0);
        ref<ConstantExpr> outparam = ConstantExpr::alloc(f.bitcastToAPInt());
        wos->write(offset, outparam);
        state.fps_produced.push_back(f.convertToDouble());
      }
      retExpr = expr_true;
      return true;
    }
    state.fps_produced.push_back(APFloat::getInf(APFloat::IEEEdouble).convertToDouble());
    return false;
  } else {

    // otherwise, we must be in a replay mode
    if (!state.fps_produced.empty()) {

      APFloat value(state.fps_produced.front());
      state.fps_produced.pop_front();
      if (!value.isInfinity()) {

        // not the flag value, so write back the next value in sequence
        ObjectPair op;
        LocalExecutor::ResolveResult res = executor->resolveMO(state, ptr, op);
        if (res == LocalExecutor::ResolveResult::OK) {
          const MemoryObject *mo = op.first;
          const ObjectState *os = op.second;
          ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          ref<Expr> offset = mo->getOffsetExpr(ptr);

          ref<ConstantExpr> outparam = ConstantExpr::alloc(value.bitcastToAPInt());
          wos->write(offset, outparam);
          retExpr = expr_true;
          return true;
        }
      }
    }
  }
  return false;
}
#endif

// RLR TODO: other functions to model: memcpy, memcmp, memmove, strlen, strcpy,

}
