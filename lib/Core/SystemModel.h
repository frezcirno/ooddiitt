

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
  bool Execute(ExecutionState &state, llvm::Function *fn, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &ret);

  static void filterHandledFunctions(std::set<const llvm::Value*> &fns);
  static void filterHandledGlobals(std::set<const llvm::Value*> &gbs);

private:
  bool ExecuteWrite(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteRead(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteIsaTTY(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturn0_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturn1_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturnMinus1_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturn42_32(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturnMinus1_64(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteNoop(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturnFirstArg(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteMemset(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);

  LocalExecutor *executor;
  const ModelOptions &opts;
  std::map<llvm::Function*,model_handler_t> dispatch;
  std::set<std::string> modeled_names;

  KInstruction *ki;
  llvm::Function *fn;

  static const std::vector<handler_descriptor_t> modeled_fns;
  static const std::vector<handler_descriptor_t> output_fns;
};

} // namespace

#endif // KLEE_SYSTEMMODEL_H
