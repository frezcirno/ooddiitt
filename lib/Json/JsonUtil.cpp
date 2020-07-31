//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/util/JsonUtil.h"

#include "klee/Internal/Module/KModule.h"

using namespace llvm;
using namespace klee;
using namespace std;
namespace fs=boost::filesystem;

void applyDiffInfo(Json::Value &root, KModule *kmod) {

  if (!root.isNull()) {
    kmod->prev_module = root["prev-module"]["name"].asString();
    kmod->post_module = root["post-module"]["name"].asString();
    kmod->is_prev_module = (kmod->prev_module == kmod->getModuleIdentifier());

    Json::Value &fns = root["functions"];
    if (kmod->isPostModule()) {
      Json::Value &fns_added = fns["added"];
      for (unsigned idx = 0, end = fns_added.size(); idx < end; ++idx) {
        kmod->addDiffFnAdded(fns_added[idx].asString());
      }
    } else {
      Json::Value &fns_removed = fns["removed"];
      for (unsigned idx = 0, end = fns_removed.size(); idx < end; ++idx) {
        kmod->addDiffFnRemoved(fns_removed[idx].asString());
      }
    }
    Json::Value &fns_body = fns["body"];
    for (unsigned idx = 0, end = fns_body.size(); idx < end; ++idx) {
      string str = fns_body[idx].asString();
      kmod->addDiffFnChangedBody(str);
    }
    Json::Value &fns_sig = fns["signature"];
    for (unsigned idx = 0, end = fns_sig.size(); idx < end; ++idx) {
      string str = fns_sig[idx].asString();
      kmod->addDiffFnChangedSig(str);
    }

    Json::Value &gbs = root["globals"];
    if (kmod->isPostModule()) {
      Json::Value &gbs_added = gbs["added"];
      for (unsigned idx = 0, end = gbs_added.size(); idx < end; ++idx) {
        kmod->addDiffGlobalAdded(gbs_added[idx].asString());
      }
    } else {
      Json::Value &gbs_removed = gbs["removed"];
      for (unsigned idx = 0, end = gbs_removed.size(); idx < end; ++idx) {
        kmod->addDiffGlobalRemoved(gbs_removed[idx].asString());
      }
    }

    Json::Value &gbs_type = gbs["changed"];
    for (unsigned idx = 0, end = gbs_type.size(); idx < end; ++idx) {
      string str = gbs_type[idx].asString();
      kmod->addDiffGlobalChanged(str);
    }

    // collect map of sets of targeted c-source statements
    string targeted_key = (kmod->isPrevModule() ? "prev-module" : "post-module");
    Json::Value &module = root[targeted_key];
    Json::Value &srcs = module["sources"];

    map<string, set<unsigned>> targeted_stmts;
    for (auto src_itr = srcs.begin(), src_end = srcs.end(); src_itr != src_end; ++src_itr) {
      fs::path path(src_itr.key().asString());
      string src_name = path.filename().string();
      Json::Value &src_entry = *src_itr;
      if (src_entry.isObject()) {
        Json::Value &line_array = src_entry["lines"];
        if (line_array.isArray()) {
          set<unsigned> &stmts = targeted_stmts[src_name];
          for (unsigned idx = 0, end = line_array.size(); idx < end; ++idx) {
            stmts.insert(line_array[idx].asUInt());
          }
        }
      }
    }
    kmod->setTargetStmts(targeted_stmts);
  }
}


