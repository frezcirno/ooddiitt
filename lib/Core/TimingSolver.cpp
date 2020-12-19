//===-- TimingSolver.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "TimingSolver.h"

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

bool TimingSolver::evaluate(const ExecutionState& state, ref<Expr> expr, Solver::Validity &result) {
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE->isTrue() ? Solver::True : Solver::False;
    return true;
  }

  sys::TimeValue now = util::getWallTimeVal();

  if (simplifyExprs)
    expr = state.constraints.simplifyExpr(expr);

  if (!solver->evaluate(Query(state.constraints, expr), result)) {
    throw solver_failure();
  }

  sys::TimeValue delta = util::getWallTimeVal();
  delta -= now;
  stats::solverTime += delta.usec();
  state.queryCost += delta.usec()/1000000.;
  return true;
}

bool TimingSolver::mustBeTrue(const ExecutionState& state, ref<Expr> expr, bool &result) {
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE->isTrue() ? true : false;
    return true;
  }

  sys::TimeValue now = util::getWallTimeVal();

  if (simplifyExprs)
    expr = state.constraints.simplifyExpr(expr);

  if (!solver->mustBeTrue(Query(state.constraints, expr), result)) {
    throw solver_failure();
  }

  sys::TimeValue delta = util::getWallTimeVal();
  delta -= now;
  stats::solverTime += delta.usec();
  state.queryCost += delta.usec()/1000000.;
  return true;
}

bool TimingSolver::mustBeTrue(const ExecutionState& state, ref<Expr> expr) {

  bool result = false;
  mustBeTrue(state, expr, result);
  return result;
}

bool TimingSolver::mustBeFalse(const ExecutionState& state, ref<Expr> expr, bool &result) {
  return mustBeTrue(state, Expr::createIsZero(expr), result);
}

bool TimingSolver::mustBeFalse(const ExecutionState& state, ref<Expr> expr) {

  bool result = false;
  mustBeFalse(state, expr, result);
  return result;
}

bool TimingSolver::mayBeTrue(const ExecutionState& state, ref<Expr> expr, bool &result) {

  bool res;
  if (!mustBeFalse(state, expr, res))
    return false;
  result = !res;
  return true;
}

bool TimingSolver::mayBeTrue(const ExecutionState& state, ref<Expr> expr) {

  bool result = false;
  mayBeTrue(state, expr, result);
  return result;
}

bool TimingSolver::mayBeFalse(const ExecutionState& state, ref<Expr> expr, bool &result) {

  bool res;
  if (!mustBeTrue(state, expr, res))
    return false;
  result = !res;
  return true;
}

bool TimingSolver::mayBeFalse(const ExecutionState& state, ref<Expr> expr) {

  bool result = false;
  mayBeFalse(state, expr, result);
  return result;
}


bool TimingSolver::getValue(const ExecutionState& state, ref<Expr> expr, ref<ConstantExpr> &result) {
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE;
    return true;
  }

  sys::TimeValue now = util::getWallTimeVal();

  if (simplifyExprs)
    expr = state.constraints.simplifyExpr(expr);

  if (!solver->getValue(Query(state.constraints, expr), result)) {
    throw solver_failure();
  }

  sys::TimeValue delta = util::getWallTimeVal();
  delta -= now;
  stats::solverTime += delta.usec();
  state.queryCost += delta.usec()/1000000.;
  return true;
}

bool TimingSolver::getInitialValues(const ExecutionState &state, const std::vector<const Array *> &objects,
                                    std::vector<std::vector<unsigned char>> &result) {

  bool have_solution = true;

  if (!objects.empty()) {
    sys::TimeValue now = util::getWallTimeVal();
    have_solution = solver->getInitialValues(Query(state.constraints, ConstantExpr::alloc(0, Expr::Bool)), objects, result);
    sys::TimeValue delta = util::getWallTimeVal();
    delta -= now;
    stats::solverTime += delta.usec();
    state.queryCost += delta.usec() / 1000000.;
  }
  return have_solution;
}

std::pair< ref<Expr>, ref<Expr> > TimingSolver::getRange(const ExecutionState& state, ref<Expr> expr) {
  return solver->getRange(Query(state.constraints, expr));
}
