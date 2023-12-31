//===-- CoreSolver.cpp ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/CommandLine.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Solver.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <string>
#include <sys/resource.h>

#ifdef ENABLE_METASMT

#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
#include <metaSMT/backend/Boolector.hpp>

#define Expr VCExpr
#define Type VCType
#define STP STP_Backend
#include <metaSMT/backend/STP.hpp>
#undef Expr
#undef Type
#undef STP

using namespace klee;
using namespace metaSMT;
using namespace metaSMT::solver;

static klee::Solver *handleMetaSMT() {
  Solver *coreSolver = NULL;
  std::string backend;
  switch (MetaSMTBackend) {
  case METASMT_BACKEND_STP:
    backend = "STP";
    coreSolver = new MetaSMTSolver<DirectSolver_Context<STP_Backend> >(
        UseForkedCoreSolver, CoreSolverOptimizeDivides);
    break;
  case METASMT_BACKEND_Z3:
    backend = "Z3";
    coreSolver = new MetaSMTSolver<DirectSolver_Context<Z3_Backend> >(
        UseForkedCoreSolver, CoreSolverOptimizeDivides);
    break;
  case METASMT_BACKEND_BOOLECTOR:
    backend = "Boolector";
    coreSolver = new MetaSMTSolver<DirectSolver_Context<Boolector> >(
        UseForkedCoreSolver, CoreSolverOptimizeDivides);
    break;
  default:
    llvm_unreachable("Unrecognised MetaSMT backend");
    break;
  };
  klee_message("Starting MetaSMTSolver(%s)", backend.c_str());
  return coreSolver;
}
#endif /* ENABLE_METASMT */

namespace klee {

Solver *createCoreSolver(CoreSolverType cst) {
  switch (cst) {
  case STP_SOLVER:
#ifdef ENABLE_STP
    {
      // tired of forgetting to manually remove stack limits
      struct rlimit rlim = { RLIM_INFINITY, RLIM_INFINITY };
      if (setrlimit(RLIMIT_STACK, &rlim) < 0) {
        klee_error("Failed to remove stack limits");
      }
    }
    return new STPSolver(UseForkedCoreSolver, CoreSolverOptimizeDivides);
#else
    llvm::errs() << "Not compiled with STP support\n";
    return NULL;
#endif
  case METASMT_SOLVER:
#ifdef ENABLE_METASMT
    llvm::outs() << "Using MetaSMT solver backend\n";
    return handleMetaSMT();
#else
    llvm::errs() << "Not compiled with MetaSMT support\n";
    return NULL;
#endif
  case DUMMY_SOLVER:
    return createDummySolver();
  case Z3_SOLVER:
#ifdef ENABLE_Z3
    return new Z3Solver();
#else
    klee_message("Not compiled with Z3 support");
    return NULL;
#endif
  case NO_SOLVER:
    llvm::errs() << "Invalid solver\n";
    return NULL;
  default:
    llvm_unreachable("Unsupported CoreSolverType");
  }
}
}
