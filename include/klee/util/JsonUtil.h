//===-----------------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#pragma once

#include <string>
#include <json/json.h>

namespace klee {
class KModule;
class TestCase;

bool applyDiffInfo(Json::Value &root, KModule *kmod);
bool loadTestCase(Json::Value &root, TestCase &test);
bool translateDifftoModule(Json::Value &root, std::string &module_name);
bool translateDifftoModule(Json::Value &root, std::string &module_name, std::string &entry_point);

} // end klee namespace
