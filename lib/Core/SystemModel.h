

#ifndef KLEE_SYSTEMMODEL_H
#define KLEE_SYSTEMMODEL_H

#include <llvm/Support/CallSite.h>
#include <klee/Expr.h>
#include <functional>

namespace klee {

class LocalExecutor;
class ExecutionState;

struct ModelOptions {
  bool doModelStdOutput;

  ModelOptions()
      : doModelStdOutput(false)
  {}
};

class SystemModel {

  typedef bool handler_t(ExecutionState&,std::vector<ref<Expr> >&args,ref<Expr>&);
  typedef handler_t SystemModel::* model_handler_t;
  typedef std::pair<std::string,model_handler_t> handler_descriptor_t;

public:
  SystemModel(LocalExecutor *e, const ModelOptions &o);
  virtual ~SystemModel() {}

  void GetModeledExternals(std::set<std::string> &names) const;
  bool ShouldBeModeled(const std::string &name) const;
  bool Execute(ExecutionState &state, llvm::Function *fn, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &ret);

private:
  bool ExecuteWrite(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteIsaTTY(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturn0(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturn1(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteNoop(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturnFirstArg(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteMemset(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);

  LocalExecutor *executor;
  const ModelOptions &opts;
  std::map<llvm::Function*,model_handler_t> dispatch;
  std::set<std::string> modeled_names;
};

} // namespace

#endif // KLEE_SYSTEMMODEL_H
