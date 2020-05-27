

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
  typedef std::pair<handler_t SystemModel::*,unsigned> model_handler_t;
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
  bool ExecuteReturnNull(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteReturnFirstArg(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteMemset(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteFloor(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteRint(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteFabs(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteModf(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteMemcpy(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteStrcmp(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteStrlen(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteStrchr(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteStrcpy(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);
  bool ExecuteStrspn(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);

  bool ExecuteOAssertFail(ExecutionState &state, std::vector<ref<Expr> >&args, ref<Expr> &retExpr);

#if 0 == 1
  bool canConstrainString(ExecutionState &state, const ObjectState *os, unsigned index, const std::string &str);
  bool doConstrainString(ExecutionState &state, const ObjectState *os, unsigned index, const std::string &str);
#endif

  LocalExecutor *executor;
  const ModelOptions &opts;
  std::map<llvm::Function*,model_handler_t> dispatch;
  std::set<std::string> modeled_names;

  KInstruction *ki;
  llvm::Function *fn;
  unsigned ctx_id;

  static const std::vector<handler_descriptor_t> modeled_fns;
  static const std::vector<handler_descriptor_t> output_fns;
  static const ref<ConstantExpr> expr_true;
  static const ref<ConstantExpr> expr_false;

};

} // namespace

#endif // KLEE_SYSTEMMODEL_H
