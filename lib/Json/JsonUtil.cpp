//===-----------------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/util/JsonUtil.h"

#include "klee/Internal/Module/KModule.h"
#include "klee/TestCase.h"

using namespace llvm;
using namespace std;
namespace fs = boost::filesystem;

namespace klee {

bool applyDiffInfo(Json::Value &root, KModule *kmod) {

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

    map<string, set_ex<unsigned>> targeted_stmts;
    for (auto src_itr = srcs.begin(), src_end = srcs.end(); src_itr != src_end; ++src_itr) {
      fs::path path(src_itr.key().asString());
      string src_name = path.filename().string();
      Json::Value &src_entry = *src_itr;
      if (src_entry.isObject()) {
        Json::Value &line_array = src_entry["lines"];
        if (line_array.isArray()) {
          set_ex<unsigned> &stmts = targeted_stmts[src_name];
          for (unsigned idx = 0, end = line_array.size(); idx < end; ++idx) {
            stmts.insert(line_array[idx].asUInt());
          }
        }
      }
    }
    kmod->setTargetStmts(targeted_stmts);
    return true;
  }
  return false;
}

bool loadTestCase(Json::Value &root, TestCase &test) {

  if (!root.isNull()) {

    // complete test case from json structure
    test.arg_c = root["argC"].asInt();
    test.arg_v = root["argV"].asString();

    test.module_name = root["module"].asString();
    test.file_name = root["file"].asString();
    test.entry_fn = root["entryFn"].asString();
    test.klee_version = root["kleeRevision"].asString();
    test.lazy_alloc_count = root["lazyAllocationCount"].asUInt();
    test.lazy_string_length = root["lazyStringLength"].asUInt();
    test.max_lazy_depth = root["maxLazyDepth"].asUInt();
    test.max_loop_forks = root["maxLoopForks"].asUInt();
    test.max_loop_iter = root["maxLoopIteration"].asUInt();
    test.message = root["message"].asString();
    test.path_condition_vars = root["pathConditionVars"].asString();
    test.term_reason = (TerminateReason) root["termination"].asUInt();
    test.test_id = root["testID"].asUInt();
    test.start = to_time_point(root["timeStarted"].asString());
    test.stop = to_time_point(root["timeStopped"].asString());
    fromDataString(test.stdin_buffer, root["stdin"].asString());
    test.unconstraintFlags = UnconstraintFlagsT(root["unconstraintFlags"].asString());

    Json::Value &args = root["arguments"];
    if (args.isArray()) {
      test.arguments.reserve(args.size());
      for (unsigned idx = 0, end = args.size(); idx < end; ++idx) {
        string value = args[idx].asString();
        vector<unsigned char> bytes;
        fromDataString(bytes, value);
        uint64_t v = 0;
        switch (bytes.size()) {
        case 1:
          v = *((uint8_t *) bytes.data());
          break;
        case 2:
          v = *((uint16_t *) bytes.data());
          break;
        case 4:
          v = *((uint32_t *) bytes.data());
          break;
        case 8:
          v = *((uint64_t *) bytes.data());
          break;
        default:
          assert(false && "unsupported data width");
          break;
        }
        test.arguments.push_back(v);
      }
    }

    test.trace_type = (TraceType) root["traceType"].asUInt();
    Json::Value &trace = root["trace"];
    if (trace.isArray()) {
      test.trace.reserve(trace.size());
      for (unsigned idx = 0, end = trace.size(); idx < end; ++idx) {
        test.trace.push_back(trace[idx].asString());
      }
    }

    Json::Value &objs = root["objects"];
    if (objs.isArray()) {
      test.objects.reserve(objs.size());
      for (unsigned idx = 0, end = objs.size(); idx < end; ++idx) {
        Json::Value &obj = objs[idx];
        string addr = obj["addr"].asString();
        unsigned count = obj["count"].asUInt();
        string data = obj["data"].asString();
        size_t align = obj["align"].asInt64();
        MemKind kind = (MemKind) obj["kind"].asUInt();
        string name = obj["name"].asString();
        string type = obj["type"].asString();
        test.objects.emplace_back(TestObject(addr, count, data, align, kind, name, type));
      }
    }
    return true;
  }
  return false;
}

bool translateDifftoModule(Json::Value &root, string &module_name) {

  if (!root.isNull() && (module_name.front() == '@')) {

    vector<string> names;
    boost::split(names, module_name.substr(1), [](char c){return c == ',';});
    for (auto str : names) {
      string name = str + "-module";
      if (root.isMember(name)) {
        module_name = root[name]["name"].asString();
        return true;
      }
    }
    klee_error("unable to find target in diff file: %s", module_name.c_str());
  }
  return false;
}

bool translateDifftoModule(Json::Value &root, string &module_name, string &entry_point) {

  vector<string> elements;
  boost::split(elements, module_name, boost::is_any_of(":"));
  if (elements.size() > 1) {
    if (translateDifftoModule(root, elements[0])) {

      module_name = elements[0];
      unsigned idx = std::stoul(elements[1]);
      Json::Value &entries = root["entryPoints"];
      if (entries.isArray() && idx < entries.size()) {
        Json::Value &entry = entries[idx];
        entry_point = entry["function"].asString();
        return true;
      }
      klee_error("index out-of-range in diff file: %u", idx);
    }
  }
  return false;
}

} // end klee namespace
