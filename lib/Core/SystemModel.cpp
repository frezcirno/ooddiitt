

#include <set>
#include <string>
#include "LocalExecutor.h"
#include "SystemModel.h"

using namespace std;
using namespace llvm;

namespace klee {

// RLR TODO : see uclibc stdio for output functions
// *printf -> returns num chars written
// (f)putc -> returns written character
// (f)puts -> returns 1
// putchar -> returns written character
// perror -> void


SystemModel::SystemModel(LocalExecutor *e, const ModelOptions &o) : executor(e), opts(o) {

  vector<handler_descriptor_t> modeled_fns = {
      { "write", &SystemModel::ExecuteWrite },
      { "isatty", &SystemModel::ExecuteIsaTTY }
  };

  Module *module = executor->getKModule()->module;
  for (const auto &pr : modeled_fns) {
    if (Function *fn = module->getFunction(pr.first)) {
      modeled_names.insert(pr.first);
      dispatch[fn] = pr.second;
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

}
