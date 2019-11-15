

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
      {"getegid", &SystemModel::ExecuteReturn0}
  };

  static const vector<handler_descriptor_t> output_fns = {
      { "printf", &SystemModel::ExecuteReturn1},
      { "fprintf", &SystemModel::ExecuteReturn1},
      { "vprintf", &SystemModel::ExecuteReturn1},
      { "vfprintf", &SystemModel::ExecuteReturn1},
      { "puts", &SystemModel::ExecuteReturn1},
      { "fputs", &SystemModel::ExecuteReturn1},
      { "fputs_unlocked", &SystemModel::ExecuteReturn1},
      { "putchar", &SystemModel::ExecuteFirstArg},
      { "putc", &SystemModel::ExecuteFirstArg},
      { "fputc", &SystemModel::ExecuteFirstArg},
      { "putchar_unlocked", &SystemModel::ExecuteFirstArg},
      { "putc_unlocked", &SystemModel::ExecuteFirstArg},
      { "fputc_unlocked", &SystemModel::ExecuteFirstArg},
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
