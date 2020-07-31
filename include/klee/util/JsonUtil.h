//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//


#pragma once

#include <json/json.h>

namespace klee {
class KModule;
}

void applyDiffInfo(Json::Value &root, klee::KModule *kmod);
