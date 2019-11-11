

#include <set>
#include <string>
#include "LocalExecutor.h"
#include "SystemModel.h"

using namespace std;
using namespace llvm;

namespace klee {

SystemModel::SystemModel(LocalExecutor *e, const ModelOptions &o) : executor(e), opts(o) {

  vector<handler_descriptor_t> modeled_fns = {
      { "write", &SystemModel::ExecuteWrite, true },
      { "isatty", &SystemModel::ExecuteIsaTTY, true },

      { "printf", &SystemModel::ExecuteReturn1, false },
      { "fprintf", &SystemModel::ExecuteReturn1, false },
      { "vprintf", &SystemModel::ExecuteReturn1, false },
      { "vfprintf", &SystemModel::ExecuteReturn1, false },

      { "puts", &SystemModel::ExecuteReturn1, false },
      { "fputs", &SystemModel::ExecuteReturn1, false },
      { "fputs_unlocked", &SystemModel::ExecuteReturn1, false },

      { "putchar", &SystemModel::ExecuteFirstArg, false },
      { "putc", &SystemModel::ExecuteFirstArg, false },
      { "fputc", &SystemModel::ExecuteFirstArg, false },
      { "putchar_unlocked", &SystemModel::ExecuteFirstArg, false },
      { "putc_unlocked", &SystemModel::ExecuteFirstArg, false },
      { "fputc_unlocked", &SystemModel::ExecuteFirstArg, false },

      { "perror", &SystemModel::ExecuteNoop, false },

      { "posix_fadvise", &SystemModel::ExecuteReturn0, true },
      { "getuid", &SystemModel::ExecuteReturn0, true },
      { "geteuid", &SystemModel::ExecuteReturn0, true },
      { "getgid", &SystemModel::ExecuteReturn0, true },
      { "getegid", &SystemModel::ExecuteReturn0, true }
  };

  Module *module = executor->getKModule()->module;
  for (const auto &tpl : modeled_fns) {
    if (Function *fn = module->getFunction(get<0>(tpl))) {
      if (opts.doModelStdOutput || get<2>(tpl)) {
        modeled_names.insert(get<0>(tpl));
        dispatch[fn] = get<1>(tpl);
      }
    }
  }
}

void SystemModel::GetModeledExternals(set<string> &names) const {

  names.insert(modeled_names.begin(), modeled_names.end());
}

bool SystemModel::Execute(ExecutionState &state, Function *fn, KInstruction *ki, const CallSite &cs, ref<Expr> &ret) {

  auto itr = dispatch.find(fn);
  if (itr != dispatch.end()) {
    handler_t SystemModel::*handler = itr->second;
    (this->*handler)(state, ki, cs, ret);
    return true;
  }
  return false;
}

void SystemModel::ExecuteWrite(ExecutionState &state, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &retExpr) {

  retExpr = executor->eval(ki, 3, state).value;
}

void SystemModel::ExecuteIsaTTY(ExecutionState &state, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &retExpr) {

  unsigned result = 0;
  ref<Expr> fd = executor->eval(ki, 1, state).value;
  if (isa<ConstantExpr>(fd)) {
    ref<ConstantExpr> cfd = cast<ConstantExpr>(fd);
    unsigned desc = cfd->getZExtValue(Expr::Int32);
    if (desc < 3) result = 1;
  }
  retExpr = ConstantExpr::create(result, Expr::Int32);
}

void SystemModel::ExecuteReturn1(ExecutionState &state, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(1, Expr::Int32);
}

void SystemModel::ExecuteReturn0(ExecutionState &state, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &retExpr) {

  retExpr = ConstantExpr::create(0, Expr::Int32);
}

void SystemModel::ExecuteNoop(ExecutionState &state, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &retExpr) {

}

void SystemModel::ExecuteFirstArg(ExecutionState &state, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &retExpr) {

  retExpr = executor->eval(ki, 1, state).value;
}


}
