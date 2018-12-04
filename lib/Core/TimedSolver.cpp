//===-- TimingSolver.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "TimedSolver.h"

#include "klee/Config/Version.h"
#include "klee/ExecutionState.h"
#include "klee/Solver.h"
#include "klee/Statistics.h"
#include "klee/Internal/System/Time.h"

#include "CoreStats.h"

#include "llvm/Support/TimeValue.h"

using namespace klee;
using namespace llvm;

/***/

bool TimedSolver::mustBeTrue(const ExecutionState &state, ref<Expr> expr, bool &result) {

  solver->setTimeout(default_timeout);
  bool succ = solver->mustBeTrue(state, expr, result);
  solver->setTimeout(0);
  return succ;
}

bool TimedSolver::mustBeFalse(const ExecutionState &state, ref<Expr> expr, bool &result) {

  solver->setTimeout(default_timeout);
  bool succ = solver->mustBeFalse(state, expr, result);
  solver->setTimeout(0);
  return succ;
}

bool TimedSolver::mayBeTrue(const ExecutionState &state, ref<Expr> expr, bool &result) {

  solver->setTimeout(default_timeout);
  bool succ = solver->mayBeTrue(state, expr, result);
  solver->setTimeout(0);
  return succ;
}

bool TimedSolver::mayBeFalse(const ExecutionState &state, ref<Expr> expr, bool &result) {

  solver->setTimeout(default_timeout);
  bool succ = solver->mayBeFalse(state, expr, result);
  solver->setTimeout(0);
  return succ;
}

bool TimedSolver::getValue(const ExecutionState &state, ref<Expr> expr, ref<ConstantExpr> &result) {

  solver->setTimeout(default_timeout);
  bool succ = solver->getValue(state, expr, result);
  solver->setTimeout(0);
  return succ;
}
