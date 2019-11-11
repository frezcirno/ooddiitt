//===-- SeedInfo.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Internal/System/Memory.h"
#include "SeedInfo.h"
#include "TimingSolver.h"

#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/util/ExprUtil.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/Support/ErrorHandling.h"

using namespace klee;

KTestObject *SeedInfo::getNextInput(const MemoryObject *mo,
                                   bool byName) {
  assert(false);
}

void SeedInfo::patchSeed(const ExecutionState &state,
                         ref<Expr> condition,
                         TimingSolver *solver) {
  assert(false);

}
