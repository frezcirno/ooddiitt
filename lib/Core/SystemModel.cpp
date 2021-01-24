

#include <set>
#include <string>
#include "LocalExecutor.h"
#include "TimingSolver.h"
#include "SystemModel.h"
#include "limits"

using namespace std;
using namespace llvm;

#define CTX_DEFAULT 0
#define CTX_MEMCPY  1
#define CTX_MEMPCPY 2
#define CTX_STRCMP  3
#define CTX_STRNCMP 4
#define CTX_MEMCMP  5
#define CTX_STRLEN  6
#define CTX_STRNLEN 7
#define CTX_STRCHR  8
#define CTX_STRRCHR 9
#define CTX_MEMCHR  10
#define CTX_STRCPY  11
#define CTX_STRNCPY 12
#define CTX_STRSPN  13
#define CTX_STRCSPN 14

namespace klee {

const vector<SystemModel::handler_descriptor_t> SystemModel::modeled_fns = {
    {"write", {&SystemModel::ExecuteWrite, CTX_DEFAULT}},
    {"read", {&SystemModel::ExecuteRead, CTX_DEFAULT}},
    {"isatty", {&SystemModel::ExecuteIsaTTY, CTX_DEFAULT}},
    {"posix_fadvise", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"is_selinux_enabled", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"kill", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"nanosleep", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"getpid", {&SystemModel::ExecuteReturn42_32, CTX_DEFAULT}},
    {"getuid", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"geteuid", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"getgid", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"getegid", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"lseek64", {&SystemModel::ExecuteReturnMinus1_64, CTX_DEFAULT}},
    {"lseek", {&SystemModel::ExecuteReturnMinus1_64, CTX_DEFAULT}},
    {"open", {&SystemModel::ExecuteReturnMinus1_32, CTX_DEFAULT}},
    {"openat", {&SystemModel::ExecuteReturnMinus1_32, CTX_DEFAULT}},
    {"close", {&SystemModel::ExecuteReturn0_32, CTX_DEFAULT}},
    {"fcntl", {&SystemModel::ExecuteReturnMinus1_32, CTX_DEFAULT}},
    {"floor", {&SystemModel::ExecuteFloor, CTX_DEFAULT}},
    {"rint", {&SystemModel::ExecuteRint, CTX_DEFAULT}},
    {"fabs", {&SystemModel::ExecuteFabs, CTX_DEFAULT}},
    {"modf", {&SystemModel::ExecuteModf, CTX_DEFAULT}},
    {"setlocale", {&SystemModel::ExecuteSetLocale, CTX_DEFAULT}},
    {"bindtextdomain", {&SystemModel::ExecuteReturnNull, CTX_DEFAULT}},
    {"textdomain", {&SystemModel::ExecuteReturnNull, CTX_DEFAULT}},
    {"__check_one_fd", {&SystemModel::ExecuteNoop, CTX_DEFAULT}},
    {"memset", {&SystemModel::ExecuteMemset, CTX_DEFAULT}},
    {"memcpy", {&SystemModel::ExecuteMemcpy, CTX_MEMCPY}},
    {"mempcpy", {&SystemModel::ExecuteMemcpy, CTX_MEMPCPY}},
    {"strcmp", {&SystemModel::ExecuteStrcmp2, CTX_STRCMP}},
    {"strncmp", {&SystemModel::ExecuteStrcmp2, CTX_STRNCMP}},
    {"memcmp", {&SystemModel::ExecuteStrcmp, CTX_MEMCMP}},
    {"strlen", {&SystemModel::ExecuteStrlen, CTX_STRLEN}},
    {"strnlen", {&SystemModel::ExecuteStrlen, CTX_STRNLEN}},
    {"strchr", {&SystemModel::ExecuteStrchr, CTX_STRCHR}},
    {"strrchr", {&SystemModel::ExecuteStrchr, CTX_STRRCHR}},
    {"memchr", {&SystemModel::ExecuteStrchr, CTX_MEMCHR}},
    {"strcpy", {&SystemModel::ExecuteStrcpy, CTX_STRCPY}},
    {"strncpy", {&SystemModel::ExecuteStrcpy, CTX_STRNCPY}},
    {"strspn", {&SystemModel::ExecuteStrspn, CTX_STRSPN}},
    {"strcspn", {&SystemModel::ExecuteStrspn, CTX_STRCSPN}},
    {"getpagesize", {&SystemModel::ExecuteGetPageSize, CTX_DEFAULT}},
    {"getenv", {&SystemModel::ExecuteGetEnv, CTX_DEFAULT}},
    {"malloc_usable_size", {&SystemModel::ExecuteMallocSize, CTX_DEFAULT}},
    {"__o_assert_fail", {&SystemModel::ExecuteOAssertFail, CTX_DEFAULT}}
};

const vector<SystemModel::handler_descriptor_t> SystemModel::output_fns = {
    { "printf", {&SystemModel::ExecuteReturn1_32, CTX_DEFAULT}},
    { "fprintf", {&SystemModel::ExecuteReturn1_32, CTX_DEFAULT}},
    { "vprintf", {&SystemModel::ExecuteReturn1_32, CTX_DEFAULT}},
    { "vfprintf", {&SystemModel::ExecuteReturn1_32, CTX_DEFAULT}},
    { "puts", {&SystemModel::ExecuteReturn1_32, CTX_DEFAULT}},
    { "fputs", {&SystemModel::ExecuteReturn1_32, CTX_DEFAULT}},
    { "fputs_unlocked", {&SystemModel::ExecuteReturn1_32, CTX_DEFAULT}},
    { "putchar", {&SystemModel::ExecuteReturnFirstArg, CTX_DEFAULT}},
    { "putc", {&SystemModel::ExecuteReturnFirstArg, CTX_DEFAULT}},
    { "fputc", {&SystemModel::ExecuteReturnFirstArg, CTX_DEFAULT}},
    { "putchar_unlocked", {&SystemModel::ExecuteReturnFirstArg, CTX_DEFAULT}},
    { "putc_unlocked", {&SystemModel::ExecuteReturnFirstArg, CTX_DEFAULT}},
    { "fputc_unlocked", {&SystemModel::ExecuteReturnFirstArg, CTX_DEFAULT}},
    { "perror", {&SystemModel::ExecuteNoop, CTX_DEFAULT}}
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

  UNUSED(gbs);
  // none
}

void SystemModel::GetModeledExternals(set<string> &names) const {

  names.insert(modeled_names.begin(), modeled_names.end());
}

// reads a concrete string from memory
string SystemModel::readStringAt(ExecutionState &state, ref<ConstantExpr> addr) {

  string result;

  // lookup the memory object
  ObjectPair op;
  if (executor->resolveMO(state, addr, op) == LocalExecutor::ResolveResult::OK) {
    const MemoryObject *mo = op.first;
    const ObjectState *os = op.second;
    uint64_t offset = addr->getZExtValue() - mo->address;
    uint64_t end = mo->address + os->getVisibleSize();
    while (offset < end) {
      ref<ConstantExpr> ch = dyn_cast<ConstantExpr>(os->read8(offset));
      if (!ch.isNull()) {
        if (ch->isZero()) {
          break;
        }
        result.push_back(ch->getZExtValue(Expr::Int8));
      }
      offset += 1;
    }
  }
  return result;
}

bool SystemModel::Execute(ExecutionState &state, Function *_fn, KInstruction *_ki, const CallSite &cs, ref<Expr> &ret) {

  fn = _fn;
  ki = _ki;

  auto itr = dispatch.find(fn);
  if (itr != dispatch.end()) {
    handler_t SystemModel::*handler = itr->second.first;
    ctx_id = itr->second.second;

    // create a vector of arguments
    unsigned num_args = cs.arg_size();
    vector<ref<Expr> > args;
    args.reserve(num_args);
    for (unsigned idx = 0; idx < num_args; ++idx) {
      ref<Expr> arg = executor->eval(ki, idx + 1, state).value;
      args.push_back(arg);
    }
    bool result = (this->*handler)(state, args, ret);
    ki = nullptr;
    fn = nullptr;
    return result;
  }
  return false;
}

bool SystemModel::ExecuteWrite(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 3) {

    ref<ConstantExpr> efd = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> eaddr = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    ref<ConstantExpr> ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    if (!(efd.isNull() || eaddr.isNull() || ecount.isNull())) {
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
          // RLR TODO: consider changing to readConcrete
          os->readConcreteStore(write, offset, count);
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
    if (!(efd.isNull() || eaddr.isNull())) {
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

  UNUSED(state);
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

bool SystemModel::ExecuteReturn1_32(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  UNUSED(state);
  UNUSED(args);
  retExpr = ConstantExpr::create(1, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturn0_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  UNUSED(state);
  UNUSED(args);
  retExpr = ConstantExpr::create(0, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturn42_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  UNUSED(state);
  UNUSED(args);
  retExpr = ConstantExpr::create(42, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturnMinus1_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  UNUSED(state);
  UNUSED(args);
  uint64_t val = (uint32_t) -1;
  retExpr = ConstantExpr::create(val, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteReturnMinus1_64(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  UNUSED(state);
  UNUSED(args);
  retExpr = ConstantExpr::create(-1, Expr::Int64);
  return true;
}

bool SystemModel::ExecuteNoop(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  UNUSED(state);
  UNUSED(args);
  UNUSED(retExpr);
  return true;
}

bool SystemModel::ExecuteReturnNull(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  UNUSED(state);
  UNUSED(args);
  retExpr = ConstantExpr::createPointer(0);
  return true;
}


bool SystemModel::ExecuteReturnFirstArg(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  UNUSED(state);
  if (!args.empty()) {
    retExpr = args[0];
    return true;
  }
  return false;
}

static inline const fltSemantics *fpWidthToSemantics(unsigned width) {
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
    ref<ConstantExpr> val = executor->toConstantFP(state, args[0], "ExFloor");
    APFloat result(*fpWidthToSemantics(val->getWidth()), val->getAPValue());
    result.roundToIntegral(APFloat::rmTowardNegative);
    retExpr = ConstantExpr::alloc(result.bitcastToAPInt());
    return true;
  }
  return false;
}

bool SystemModel::ExecuteRint(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 1) {
    ref<ConstantExpr> val = executor->toConstantFP(state, args[0], "ExRint");
    APFloat result(*fpWidthToSemantics(val->getWidth()), val->getAPValue());
    result.roundToIntegral(APFloat::rmNearestTiesToAway);
    retExpr = ConstantExpr::alloc(result.bitcastToAPInt());
    return true;
  }
  return false;
}

bool SystemModel::ExecuteFabs(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 1) {
    ref<ConstantExpr> val = executor->toConstantFP(state, args[0], "ExFabs");
    APFloat result(*fpWidthToSemantics(val->getWidth()), val->getAPValue());
    result.clearSign();
    retExpr = ConstantExpr::alloc(result.bitcastToAPInt());
    return true;
  }
  return false;
}

bool SystemModel::ExecuteModf(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 2) {
    ref<ConstantExpr> val = executor->toConstantFP(state, args[0], "ExModf::left");
    ref<ConstantExpr> ptr = executor->toConstantFP(state, args[1], "ExModf::right");
    APFloat result(*fpWidthToSemantics(val->getWidth()), val->getAPValue());
    APFloat integer = result;
    APFloat fraction = result;
    integer.roundToIntegral(APFloat::rmTowardZero);
    fraction.subtract(integer, APFloat::rmTowardPositive);
    ref<ConstantExpr> outparam = ConstantExpr::alloc(integer.bitcastToAPInt());

    ObjectPair op;
    if (executor->resolveMO(state, ptr, op) == LocalExecutor::ResolveResult::OK) {
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

bool SystemModel::ExecuteMemset(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  if (args.size() == 3) {

    ref<ConstantExpr> eptr = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> evalue = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    ref<ConstantExpr> ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    if (!(eptr.isNull() || evalue.isNull() || ecount.isNull())) {

      uint64_t ptr = eptr->getZExtValue();
      uint8_t value = (uint8_t) evalue->getZExtValue();
      uint64_t count = ecount->getZExtValue();
      ObjectPair op;

      // lookup the ptr object
      if (executor->resolveMO(state, eptr, op) == LocalExecutor::ResolveResult::OK) {

        const MemoryObject *mo = op.first;
        const ObjectState *os = op.second;
        uint64_t offset = ptr - mo->address;

        // make sure dest has enough room for the memset
        if (offset + count <= os->visible_size) {
          ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          for (unsigned idx = 0; idx < count; ++idx) {
            wos->write8(offset + idx, value);
          }
          retExpr = eptr;
          return true;
        } else {
          executor->terminateStateOnMemFault(state, this->ki, eptr, mo, "out-of-bounds memset");
          return true;
        }
      }
    }
  }
  return false;
}

bool SystemModel::ExecuteMemcpy(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  if (args.size() == 3) {

    ref<ConstantExpr> edst = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> esrc = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    ref<ConstantExpr> ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    if (!(edst.isNull() || esrc.isNull() || ecount.isNull())) {
      uint64_t dst = edst->getZExtValue();
      uint64_t src = esrc->getZExtValue();
      uint64_t count = ecount->getZExtValue();
      ObjectPair op;

      // lookup the src object
      if (executor->resolveMO(state, esrc, op) == LocalExecutor::ResolveResult::OK) {

        const MemoryObject *src_mo = op.first;
        const ObjectState *src_os = op.second;
        uint64_t src_offset = src - src_mo->address;

        // make sure it is long enough
        if (src_offset + count <= src_os->visible_size) {

          // lookup the dest object
          if (executor->resolveMO(state, edst, op) == LocalExecutor::ResolveResult::OK) {

            const MemoryObject *dst_mo = op.first;
            const ObjectState *dst_os = op.second;
            uint64_t dst_offset = dst - dst_mo->address;

            // make sure dest has enough room for the copy
            if (dst_offset + count <= dst_os->visible_size) {

              ObjectState *wos = state.addressSpace.getWriteable(dst_mo, dst_os);
              // if the memcpy was within the same memory object, then the old object state may
              // have been deleted.
              if (src_os == dst_os) {
                src_os = wos;
              }

              for (uint64_t idx = 0; idx < count; ++idx) {
                ref<Expr> value = src_os->read8(src_offset + idx);
                wos->write8(dst_offset + idx, value);
              }
              if (ctx_id == CTX_MEMPCPY) {
                retExpr = ConstantExpr::createPointer(dst + count);
              } else {
                retExpr = args[0];
              }
              return true;
            } else {
              executor->terminateStateOnMemFault(state, this->ki, edst, dst_mo, "out-of-bounds memcpy dest");
              return true;
            }
          }
        } else {
          executor->terminateStateOnMemFault(state, this->ki, esrc, src_mo, "out-of-bounds memcpy src");
          return true;
        }
      }
    }
  }
  return false;
}

bool SystemModel::ExecuteStrcmp(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  if (args.size() > 1) {

    ref<ConstantExpr> es1 = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> es2 = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    ref<ConstantExpr> ecount = ConstantExpr::create(numeric_limits<uint64_t>::max(), Expr::Int64);
    if (args.size() > 2) {
      ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    }
    if (!(es1.isNull() || es2.isNull() || ecount.isNull())) {
      uint64_t s1 = es1->getZExtValue();
      uint64_t s2 = es2->getZExtValue();
      uint64_t count = ecount->getZExtValue();
      ObjectPair op;

      // lookup the s1 object
      if (executor->resolveMO(state, es1, op) == LocalExecutor::ResolveResult::OK) {

        const MemoryObject *s1_mo = op.first;
        const ObjectState *s1_os = op.second;
        uint64_t s1_offset = s1 - s1_mo->address;

        // lookup the s2 object
        if (executor->resolveMO(state, es2, op) == LocalExecutor::ResolveResult::OK) {

          const MemoryObject *s2_mo = op.first;
          const ObjectState *s2_os = op.second;
          uint64_t s2_offset = s2 - s2_mo->address;

          for (unsigned idx = 0; idx < count; ++idx) {

            // check of this operation is in-bounds of both strings
            if (s1_offset + idx >= s1_os->visible_size) {
              executor->terminateStateOnMemFault(state, this->ki, es1, s1_mo, "out-of-bounds strcmp s1");
              return true;
            }
            if (s2_offset + idx >= s2_os->visible_size) {
              executor->terminateStateOnMemFault(state, this->ki, es2, s2_mo, "out-of-bounds strcmp s2");
              return true;
            }

            ref<Expr> read1 = s1_os->read8(s1_offset + idx);
            ref<Expr> read2 = s2_os->read8(s2_offset + idx);
            ref<ConstantExpr> ech1 = dyn_cast<ConstantExpr>(executor->toUnique(state, read1));
            ref<ConstantExpr> ech2 = dyn_cast<ConstantExpr>(executor->toUnique(state, read2));
            if (ech1.isNull() || ech2.isNull()) {
              // something is symbolic here, return false and do it the hard way
              return false;
            }
            int ch1 = ech1->getZExtValue(Expr::Int8);
            int ch2 = ech2->getZExtValue(Expr::Int8);
            int diff = ch1 - ch2;
            if (diff != 0) {
              retExpr = SubExpr::create(ConstantExpr::create(ch1, Expr::Int32), ConstantExpr::create(ch2, Expr::Int32));
              return true;
            } else if (ch1 == 0 && (ctx_id == CTX_STRCMP || ctx_id == CTX_STRNCMP)) {
              // diff is zero, so ch1 == ch2 and null terminator
              retExpr = ConstantExpr::create(0, Expr::Int32);
              return true;
            }
          }
          retExpr = ConstantExpr::create(0, Expr::Int32);
          return true;
        }
      }
    }
  }
  return false;
}

bool SystemModel::ExecuteStrcmp2(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  if (args.size() > 1) {

    ref<ConstantExpr> ecount = ConstantExpr::create(numeric_limits<uint64_t>::max(), Expr::Int64);
    if (args.size() > 2) {
      ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    }
    if (!ecount.isNull()) {

      ref<Expr> s1 = args[0];
      ref<Expr> s2 = args[1];
      uint64_t count = ecount->getZExtValue();
      ObjectPair op1, op2;
      uint64_t offset1, offset2;

      LocalExecutor::ResolveResult res1 = executor->resolveUniqueMO(state, s1, op1, offset1);
      LocalExecutor::ResolveResult res2 = executor->resolveUniqueMO(state, s2, op2, offset2);

      if (res1 == LocalExecutor::ResolveResult::NoObject || res2 == LocalExecutor::ResolveResult::NoObject) {
        // if either resolution found no object, then fall back to slow method
        return false;
      }
      if (res1 == LocalExecutor::ResolveResult::NullAccess || res2 == LocalExecutor::ResolveResult::NullAccess) {
        // if either was a null access, then we have a pointer violation
        const MemoryObject *mo = (res1 == LocalExecutor::ResolveResult::NullAccess) ? op1.first : op2.first;
        executor->terminateStateOnMemFault(state, this->ki, s1, mo, "null strcmp");
        return true;
      }

      // both resolved to a unique memory object
      assert(res1 == LocalExecutor::ResolveResult::OK && res2 == LocalExecutor::ResolveResult::OK);

      // same object, same offset means they are equal
      if (op1.first == op2.first && offset1 == offset2) {
        retExpr = ConstantExpr::create(0, Expr::Int32);
        return true;
      }

      // try to read the strings as concrete values
      string str1, str2;
      bool oob1, oob2;
      bool read1 = executor->readConcreteStr(state, op1.second, offset1, count, str1, oob1);
      bool read2 = executor->readConcreteStr(state, op2.second, offset2, count, str2, oob2);

      // if either trips an out-of-bound error, then terminate the state
      if (oob1 || oob2) {
        const MemoryObject *mo = oob1 ? op1.first : op2.first;
        executor->terminateStateOnMemFault(state, this->ki, s1, mo, "oob strcmp");
        return true;
      }

      if (read1 && read2) {
        // both read concretely, we can directly return the result
        retExpr = ConstantExpr::create((unsigned) s1.compare(s2), Expr::Int32);
        return true;
      } else if (read1 || read2) {
        // one was concrete the other contained a symbolic value
        // treat comparison as a single entity
        ref<Expr> byte0 = ConstantExpr::create(0, Expr::Int8);
        ref<Expr> eq = ConstantExpr::create(1, Expr::Bool);
        ref<Expr> lt = ConstantExpr::create(0, Expr::Bool);
        ref<Expr> gt = ConstantExpr::create(0, Expr::Bool);

        // select the appropriate symbolic and concrete values
        if (read1) {
          // construct three constraints describing the three possible results
          // reading from constant to symbolic
          unsigned idx = 0;
          for (const char &ch : str1) {
            ref<Expr> ch1 = ConstantExpr::create(ch, Expr::Int8);
            ref<Expr> ch2 = op2.second->read8(offset2 + idx);
            gt = OrExpr::create(gt, AndExpr::create(eq, UgtExpr::create(ch1, ch2)));
            lt = OrExpr::create(lt, AndExpr::create(eq, UltExpr::create(ch1, ch2)));
            eq = AndExpr::create(eq, EqExpr::create(ch1, ch2));
            ++idx;
          }
          if (count > str1.size()) {
            eq = AndExpr::create(eq, EqExpr::create(op2.second->read8(offset2 + idx), byte0));
          }
        } else {

          // construct three constraints describing the three possible results
          // reading from symbolic to constant
          unsigned idx = 0;
          for (const char &ch : str2) {
            ref<Expr> ch1 = op1.second->read8(offset1 + idx);
            ref<Expr> ch2 = ConstantExpr::create(ch, Expr::Int8);
            gt = OrExpr::create(gt, AndExpr::create(eq, UgtExpr::create(ch1, ch2)));
            lt = OrExpr::create(lt, AndExpr::create(eq, UltExpr::create(ch1, ch2)));
            eq = AndExpr::create(eq, EqExpr::create(ch1, ch2));
            ++idx;
          }
          if (count > str2.size()) {
            eq = AndExpr::create(eq, EqExpr::create(op1.second->read8(offset1 + idx), byte0));
          }
        }

        vector<pair<ref<Expr>, int>> constraints;
        if (executor->solver->mayBeTrue(state, eq)) constraints.push_back(make_pair(eq, 0));
        if (executor->solver->mayBeTrue(state, gt)) constraints.push_back(make_pair(gt, 1));
        if (executor->solver->mayBeTrue(state, lt)) constraints.push_back(make_pair(lt, -1));
        if (constraints.empty()) {
          // odd. none were satisfyable...
          // probably indicates that the above constraints are not exactly right
          // let the hard way try.
          errs() << "modeled strcmp: no solvable constraints" << oendl;
          return false;
        }

        for (unsigned idx = 0, end = constraints.size(); idx < end; ++idx) {
          auto &pr = constraints[idx];
          if (idx < end - 1) {
            ExecutionState *ns = executor->clone(&state);
            ns->addConstraint(pr.first);
            executor->bindLocal(ki, *ns, ConstantExpr::create((unsigned) pr.second, Expr::Int32));
          } else {
            state.addConstraint(pr.first);
            retExpr = ConstantExpr::create((unsigned) pr.second, Expr::Int32);
          }
        }
        return true;

      } else {
        // neither could be read concretely, fall back to slow method
        return false;
      }

    }
  }
  return false;
}

bool SystemModel::ExecuteStrlen(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  if (args.size() > 0) {

    ref<ConstantExpr> es = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> emaxlen = ConstantExpr::create(numeric_limits<uint64_t>::max(), Expr::Int64);
    if (args.size() > 1) {
      emaxlen = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    }
    if (!(es.isNull() || emaxlen.isNull())) {

      uint64_t s = es->getZExtValue();
      uint64_t maxlen = emaxlen->getZExtValue();
      ObjectPair op;

      // lookup the string object
      if (executor->resolveMO(state, es, op) == LocalExecutor::ResolveResult::OK) {

        const MemoryObject *mo = op.first;
        const ObjectState *os = op.second;
        uint64_t offset = s - mo->address;

        for (unsigned idx = 0; idx < maxlen; ++idx) {

          // check if read is inbounds
          if (offset + idx >= os->visible_size) {
            executor->terminateStateOnMemFault(state, this->ki, es, mo, "out-of-bounds strlen");
            return true;
          }

          ref<Expr> read = os->read8(offset + idx);
          ref<ConstantExpr> ech = dyn_cast<ConstantExpr>(executor->toUnique(state, read));
          if (ech.isNull()) {
            // something is symbolic here, return false and do it the hard way
            return false;
          }
          int ch = ech->getZExtValue(Expr::Int8);
          if (ch == 0) {
            retExpr = ConstantExpr::create(idx, Expr::Int64);
            return true;
          }
        }
        retExpr = ConstantExpr::create(maxlen, Expr::Int64);
        return true;
      }
    }
  }
  return false;
}

bool SystemModel::ExecuteStrchr(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  if (args.size() > 1) {

    ref<ConstantExpr> es = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> evalue = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    ref<ConstantExpr> emaxlen = ConstantExpr::create(numeric_limits<uint64_t>::max(), Expr::Int64);
    if (args.size() > 2) {
      emaxlen = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    }
    if (!(es.isNull() || evalue.isNull() || emaxlen.isNull())) {
      uint64_t s = es->getZExtValue();
      uint8_t value = (uint8_t) evalue->getZExtValue(Expr::Int32);
      uint64_t maxlen = emaxlen->getZExtValue();
      ObjectPair op;

      // lookup the string object
      if (executor->resolveMO(state, es, op) == LocalExecutor::ResolveResult::OK) {

        const MemoryObject *mo = op.first;
        const ObjectState *os = op.second;
        uint64_t offset = s - mo->address;
        uint64_t result = 0;

        for (unsigned idx = 0; idx < maxlen; ++idx) {
          ref<Expr> read = os->read8(offset + idx);
          ref<ConstantExpr> ech = dyn_cast<ConstantExpr>(executor->toUnique(state, read));
          if (ech.isNull()) {
            // something is symbolic here, return false and do it the hard way
            return false;
          }
          int ch = ech->getZExtValue(Expr::Int8);
          if (ch == value) {
            if (ctx_id == CTX_STRRCHR) {
              result = s + idx;
            } else {
              retExpr = ConstantExpr::createPointer(s + idx);
              return true;
            }
          }
          if (ch == 0 && (ctx_id == CTX_STRCHR || ctx_id == CTX_STRRCHR)) {
            break;
          }
        }
        retExpr = ConstantExpr::createPointer(result);
        return true;
      }
    }
  }
  return false;
}

bool SystemModel::ExecuteStrcpy(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  if (args.size() > 1) {

    ref<ConstantExpr> edst = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> esrc = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    ref<ConstantExpr> ecount = ConstantExpr::create(numeric_limits<uint64_t>::max(), Expr::Int64);
    if (args.size() > 2) {
      ecount = dyn_cast<ConstantExpr>(executor->toUnique(state, args[2]));
    }
    if (!(edst.isNull() || esrc.isNull() || ecount.isNull())) {
      uint64_t dst = edst->getZExtValue();
      uint64_t src = esrc->getZExtValue();
      uint64_t count = ecount->getZExtValue();
      ObjectPair op;

      // lookup the src object
      if (executor->resolveMO(state, esrc, op) == LocalExecutor::ResolveResult::OK) {

        const MemoryObject *src_mo = op.first;
        const ObjectState *src_os = op.second;
        uint64_t src_offset = src - src_mo->address;

        // lookup the dest object
        if (executor->resolveMO(state, edst, op) == LocalExecutor::ResolveResult::OK) {

          const MemoryObject *dst_mo = op.first;
          const ObjectState *dst_os = op.second;
          uint64_t dst_offset = dst - dst_mo->address;

          ObjectState *wos = state.addressSpace.getWriteable(dst_mo, dst_os);
          // if the memcpy was within the same memory object, then the old object state may
          // have been deleted.
          if (src_os == dst_os) {
            src_os = wos;
          }

          for (uint64_t idx = 0; idx < count; ++idx) {

            // check of this operation is in-bounds of both strings
            if (src_offset + idx >= src_os->visible_size) {
              executor->terminateStateOnMemFault(state, this->ki, esrc, src_mo, "out-of-bounds strcpy src");
              return true;
            }
            if (dst_offset + idx >= dst_os->visible_size) {
              executor->terminateStateOnMemFault(state, this->ki, edst, dst_mo, "out-of-bounds strcpy dst");
              return true;
            }

            ref<Expr> read = src_os->read8(src_offset + idx);
            ref<ConstantExpr> ech = dyn_cast<ConstantExpr>(executor->toUnique(state, read));
            if (ech.isNull()) {
              // something is symbolic here, return false and do it the hard way
              return false;
            }
            wos->write8(dst_offset + idx, ech);
            int ch = ech->getZExtValue(Expr::Int8);
            if (ch == 0) {
              break;
            }
          }
          retExpr = edst;
          return true;
        }
      }
    }
  }
  return false;
}

bool SystemModel::ExecuteStrspn(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  if (args.size() == 2) {

    ref<ConstantExpr> esrc = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    ref<ConstantExpr> elst = dyn_cast<ConstantExpr>(executor->toUnique(state, args[1]));
    if (!(esrc.isNull() || elst.isNull())) {
      uint64_t src = esrc->getZExtValue();
      uint64_t lst = elst->getZExtValue();
      ObjectPair op;

      // lookup the string object
      if (executor->resolveMO(state, esrc, op) == LocalExecutor::ResolveResult::OK) {

        const MemoryObject *src_mo = op.first;
        const ObjectState *src_os = op.second;
        uint64_t src_offset = src - src_mo->address;

        // lookup the list object
        if (executor->resolveMO(state, elst, op) == LocalExecutor::ResolveResult::OK) {

          const MemoryObject *lst_mo = op.first;
          const ObjectState *lst_os = op.second;
          uint64_t lst_offset = lst - lst_mo->address;

          set<uint8_t> char_lst;
          for (uint64_t idx = 0, end = lst_os->visible_size + 1; idx < end; ++idx) {

            // check of this operation is in-bounds of the list string
            if (lst_offset + idx >= lst_os->visible_size) {
              executor->terminateStateOnMemFault(state, this->ki, elst, lst_mo, "out-of-bounds strspn lst");
              return true;
            }

            ref<Expr> read = lst_os->read8(lst_offset + idx);
            ref<ConstantExpr> ech = dyn_cast<ConstantExpr>(executor->toUnique(state, read));
            if (ech.isNull()) {
              // something is symbolic here, return false and do it the hard way
              return false;
            }
            unsigned char ch = ech->getZExtValue(Expr::Int8);
            if (ch == 0) {
              break;
            } else {
              char_lst.insert(ch);
            }
          }

          uint64_t result = 0;
          for (uint64_t idx = 0, end = src_os->visible_size + 1; idx < end; ++idx) {

            // check of this operation is in-bounds of the src string
            if (src_offset + idx >= src_os->visible_size) {
              executor->terminateStateOnMemFault(state, this->ki, esrc, src_mo, "out-of-bounds strspn src");
              return true;
            }

            ref<Expr> read = src_os->read8(src_offset + idx);
            ref<ConstantExpr> ech = dyn_cast<ConstantExpr>(executor->toUnique(state, read));
            if (ech.isNull()) {
              // something is symbolic here, return false and do it the hard way
              return false;
            }
            unsigned char ch = ech->getZExtValue(Expr::Int8);
            if (ch == 0) {
              break;
            }
            if (ctx_id == CTX_STRSPN) {
              if (char_lst.find(ch) != char_lst.end()) {
                result += 1;
              } else {
                break;
              }
            } else {
              if (char_lst.find(ch) == char_lst.end()) {
                result += 1;
              } else {
                break;
              }
            }
          }
          retExpr = ConstantExpr::create(result, Expr::Int64);
          return true;
        }
      }
    }
  }
  return false;
}

bool SystemModel::ExecuteGetPageSize(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {

  UNUSED(state);
  UNUSED(args);
  retExpr = ConstantExpr::create(4096, Expr::Int32);
  return true;
}

bool SystemModel::ExecuteGetEnv(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 1) {
    ref<ConstantExpr> estr = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    if (!estr.isNull()) {
      string var = readStringAt(state, estr);
      retExpr = ConstantExpr::create(0, Expr::Int64);
      return true;
    }
  }
  return false;
}

bool SystemModel::ExecuteSetLocale(ExecutionState &state, std::vector<ref<Expr>> &args, ref<Expr> &retExpr) {
  UNUSED(state);
  UNUSED(args);
  if (!executor->libc_initializing) {
    uint64_t offset = 0;
    if (MemoryObject *mo = executor->findGlobalObject("__brt_klee_setlocale_name")) {
      offset = mo->address;
    }
    retExpr = ConstantExpr::createPointer(offset);
    return true;
  }
  return false;
}

bool SystemModel::ExecuteMallocSize(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  if (args.size() == 1) {
    ref<ConstantExpr> eptr = dyn_cast<ConstantExpr>(executor->toUnique(state, args[0]));
    if (!eptr.isNull()) {

      if (eptr->isZero()) {
        retExpr = ConstantExpr::create(0, Expr::Int64);
        return true;
      }

      // lookup the memory object
      ObjectPair op;
      if (executor->resolveMO(state, eptr, op) == LocalExecutor::ResolveResult::OK) {
        retExpr = ConstantExpr::create(op.second->getVisibleSize(), Expr::Int64);
        return true;
      }
    }
  }
  return false;
}


bool SystemModel::ExecuteOAssertFail(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr) {

  UNUSED(retExpr);
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

#if 0 == 1
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

#endif

} // end namespace
