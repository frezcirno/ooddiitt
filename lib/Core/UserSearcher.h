//===-- UserSearcher.h ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_USERSEARCHER_H
#define KLEE_USERSEARCHER_H

#include "Searcher.h"

namespace klee {
  class Executor;
  class Searcher;

  // XXX gross, should be on demand?
  bool userSearcherRequiresMD2U();

  Searcher *constructUserSearcher(Executor &executor);
  Searcher *constructUserSearcher(Executor &executor, const std::vector<Searcher::CoreSearchType> &lst);
  Searcher *constructUserSearcher(Executor &executor, Searcher::CoreSearchType type);
}

#endif
