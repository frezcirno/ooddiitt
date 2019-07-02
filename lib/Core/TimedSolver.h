//===-- TimingSolver.h ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_TIMEDSOLVER_H
#define KLEE_TIMEDSOLVER_H

#include "klee/Expr.h"
#include "klee/Solver.h"
#include "TimingSolver.h"

namespace klee {

  /// TimedSolver - A simple class which wraps a sets and resets the timeout
  class TimedSolver {
  private:
    TimingSolver *solver;
    double default_timeout;

  public:
    TimedSolver(TimingSolver *_solver, double _default)
      : solver(_solver), default_timeout(_default) {}
    ~TimedSolver() {
      solver = nullptr;
    }

    void setTimeout(double t) { solver->setTimeout(t); }
    bool mustBeTrue(const ExecutionState&, ref<Expr>, bool &result);
    bool mustBeFalse(const ExecutionState&, ref<Expr>, bool &result);
    bool mayBeTrue(const ExecutionState&, ref<Expr>, bool &result);
    bool mayBeFalse(const ExecutionState&, ref<Expr>, bool &result);
    bool getValue(const ExecutionState &, ref<Expr> expr, ref<ConstantExpr> &result);
  };

}

#endif
