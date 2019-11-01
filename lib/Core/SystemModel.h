

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

  typedef void handler_t(ExecutionState&,KInstruction*,const llvm::CallSite&,ref<Expr>&);
  typedef handler_t SystemModel::* model_handler_t;
  typedef std::pair<std::string,model_handler_t> handler_descriptor_t;

public:
  SystemModel(LocalExecutor *e, const ModelOptions &o);
  virtual ~SystemModel() {}

  void GetModeledExternals(std::set<std::string> & names) const;
  bool Execute(ExecutionState &state, llvm::Function *fn, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &ret);

private:
  void ExecuteWrite(ExecutionState &state, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &retExpr);
  void ExecuteIsaTTY(ExecutionState &state, KInstruction *ki, const llvm::CallSite &cs, ref<Expr> &retExpr);

  LocalExecutor *executor;
  ModelOptions opts;
  std::map<llvm::Function*,model_handler_t> dispatch;
  std::set<std::string> modeled_names;
};

} // namespace

#endif // KLEE_SYSTEMMODEL_H
