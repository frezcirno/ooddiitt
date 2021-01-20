//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"
#include "klee/Internal/Support/PrintVersion.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Analysis/CallGraph.h"

#include "json/json.h"

#include <string>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include "klee/util/CommonUtil.h"

using namespace llvm;
using namespace klee;
using namespace std;
namespace alg = boost::algorithm;
namespace fs = boost::filesystem;

namespace {
cl::OptionCategory BrtCategory("specific brt options");
cl::opt<string> InputFile1(cl::desc("<original bytecode>"), cl::Positional, cl::Required);
cl::opt<string> InputFile2(cl::desc("<updated bytecode>"), cl::Positional, cl::Required);
cl::opt<string> InputFile3(cl::desc("<oracle bytecode>"), cl::Positional);
cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::cat(BrtCategory));
cl::opt<bool> Verbose("verbose", cl::init(false), cl::desc("Emit verbose output"), cl::cat(BrtCategory));
cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"), cl::cat(BrtCategory));
}

//===----------------------------------------------------------------------===//
// main Driver function
//

void diffFns(KModule *kmod1,
             KModule *kmod2,
             Json::Value &added,
             Json::Value &removed,
             set_ex<string> &sig,
             set_ex<string> &body,
             set_ex<string> &commons) {

  set_ex<string> fn_names1;
  set_ex<string> fn_names2;

  kmod1->getUserFunctions(fn_names1);
  kmod2->getUserFunctions(fn_names2);

  // find the functions that have been added (in 2 but not in 1)
  set_ex<string> fns_added;
  set_difference(fn_names2.begin(), fn_names2.end(), fn_names1.begin(), fn_names1.end(), inserter(fns_added, fns_added.end()));
  for (auto fn : fns_added) added.append(fn);

  // find the functions that have been removed (in 1 but not in 2)
  set_ex<string> fns_removed;
  set_difference(fn_names1.begin(), fn_names1.end(), fn_names2.begin(), fn_names2.end(), inserter(fns_removed, fns_removed.end()));
  for (auto fn : fns_removed) removed.append(fn);

  // those that are in both will need further checks
  set_ex<string> fns_both;
  set_intersection(fn_names1.begin(), fn_names1.end(), fn_names2.begin(), fn_names2.end(), inserter(fns_both, fns_both.end()));

  vector<pair<KFunction*,KFunction*> > fn_pairs;
  fn_pairs.reserve(fns_both.size());
  for (auto fn : fns_both) {
    fn_pairs.emplace_back(make_pair(kmod1->getKFunction(fn), kmod2->getKFunction(fn)));
  }

  // check function signatures
  for (const auto &pr : fn_pairs) {
    assert(pr.first && pr.second);

    KFunction *kf1 = pr.first;
    KFunction *kf2 = pr.second;
    string fn_name = kf1->getName();

    if (!ModuleTypes::isEquivalentType(kf1->function->getFunctionType(), kf2->function->getFunctionType())) {
      sig.insert(fn_name);
    } else if (kf1->getHash() != kf2->getHash()) {
      body.insert(fn_name);
    } else {
      commons.insert(fn_name);
    }
  }
}


void createInverseHashMap(KModule *kmod, KFunction *kf, map<uint64_t, vector<unsigned>> &inv_map) {

  // for each bblock in kf, insert hash and block id
  Function *fn = kf->function;
  for (auto fn_itr = fn->begin(), fn_end = fn->end(); fn_itr != fn_end; ++fn_itr) {
    BasicBlock *bb = fn_itr;
    unsigned id = kmod->getBBlockID(bb);
    if (id != 0) {
      auto &lst = inv_map[kf->getHash(bb)];
      lst.push_back(id);
    }
  }
}

void findModifiedBlocks(KModule *kmod1, KModule *kmod2, const string &name, set_ex<unsigned> &bb1, set_ex<unsigned> &bb2) {

  KFunction *kf1 = kmod1->getKFunction(name);
  KFunction *kf2 = kmod2->getKFunction(name);

  map<uint64_t, vector<unsigned>> inv_map1, inv_map2;
  createInverseHashMap(kmod1, kf1, inv_map1);
  createInverseHashMap(kmod2, kf2, inv_map2);

  // now remove the common entries and insert remaining blocks into bb lists
  deque<uint64_t> common_hashes;
  for (const auto &itr1 : inv_map1) {
    uint64_t hash = itr1.first;
    const auto &itr2 = inv_map2.find(hash);
    if ((itr2 != inv_map2.end()) && (itr1.second.size() == itr2->second.size())) {
      common_hashes.push_back(hash);
    }
  }

  // remove the common hashes
  for (auto hash : common_hashes) {
    inv_map1.erase(hash);
    inv_map2.erase(hash);
  }

  // remaining are unique blocks
  for (const auto &itr : inv_map1) {
    for (auto bb_id : itr.second) {
      bb1.insert(bb_id);
    }
  }

  for (const auto &itr : inv_map2) {
    for (auto bb_id : itr.second) {
      bb2.insert(bb_id);
    }
  }
}

void diffGbs(KModule *kmod1, KModule *kmod2, Json::Value &added, Json::Value &removed, Json::Value &changed) {

  set_ex<string> gb_names1;
  set_ex<string> gb_names2;

  kmod1->getUserGlobals(gb_names1);
  kmod2->getUserGlobals(gb_names2);

  // find the globals that have been added (in 2 but not in 1)
  set_ex<string> gbs_added;
  set_difference(gb_names2.begin(), gb_names2.end(), gb_names1.begin(), gb_names1.end(), inserter(gbs_added, gbs_added.end()));
  for (auto gb : gbs_added) added.append(gb);

  // find the globals that have been removed (in 1 but not in 2)
  set_ex<string> gbs_removed;
  set_difference(gb_names1.begin(), gb_names1.end(), gb_names2.begin(), gb_names2.end(), inserter(gbs_removed, gbs_removed.end()));
  for (auto gb : gbs_removed) removed.append(gb);

  // those that are in both will need further checks
  set_ex<string> gbs_both;
  set_intersection(gb_names1.begin(), gb_names1.end(), gb_names2.begin(), gb_names2.end(), inserter(gbs_both, gbs_both.end()));

  Module *mod1 = kmod1->module;
  Module *mod2 = kmod2->module;
  assert(mod1 && mod2);
  vector<pair<GlobalVariable*,GlobalVariable*> > gb_pairs;
  gb_pairs.reserve(gbs_both.size());
  for (auto gb : gbs_both) {
    gb_pairs.emplace_back(make_pair(mod1->getNamedGlobal(gb), mod2->getNamedGlobal(gb)));
  }

  for (const auto &pr : gb_pairs) {
    assert(pr.first && pr.second);
    if (!ModuleTypes::isEquivalentType(pr.first->getType(), pr.second->getType())) {
      changed.append(pr.first->getName().str());
    }
  }
}

void calcDistanceMap(Module *mod,
                     const map<Function*,set<Function*>> &callee_graph,
                     const set<string> &sources, const set<Function*> &sinks,
                     map<string,unsigned> &distance_map) {

  set<Function*> srcs;
  for (const auto &str : sources) {
    if (Function *fn = mod->getFunction(str)) srcs.insert(fn);
  }

  set<Function*> scope(sinks.begin(), sinks.end());
  unsigned prior_size = 0;
  unsigned depth = 0;

  while (prior_size != scope.size()) {
    prior_size = scope.size();
    depth += 1;

    set<Function*> worklist(scope);
    for (Function *fn : worklist) {
      auto itr = callee_graph.find(fn);
      if (itr != callee_graph.end()) {
        const auto &callers = itr->second;
        scope.insert(callers.begin(), callers.end());
      }
    }
    for (Function *fn : srcs) {
      string name = fn->getName();
      if ((distance_map.find(name) == distance_map.end()) && (scope.find(fn) != scope.end())) {
        distance_map.insert(make_pair(name, depth));
      }
    }
  }
}

void reachesFns(KModule *kmod,
                const map<Function*,set<Function*>> &callee_graph,
                const set<string> &sources,
                const set<string> &changed,
                map<string,unsigned> &map) {

  // construct a target set of changed functions
  set<Function*> sinks;
  for (const auto &fn_name : changed) {
    if (Function *fn = kmod->getFunction(fn_name)) {
      sinks.insert(fn);
      map.insert(make_pair(fn->getName(), 0));
    }
  }
  calcDistanceMap(kmod->module, callee_graph, sources, sinks, map);
}

void addReaching(Function *fn, const map<Function*,set<Function*>> &caller_graph, set<Function*> &reaching) {

  deque<Function*> worklist;
  worklist.push_back(fn);

  while (!worklist.empty()) {
    Function *curr = worklist.front();
    worklist.pop_front();

    auto ins = reaching.insert(curr);
    if (ins.second) {
      auto itr = caller_graph.find(curr);
      if (itr != caller_graph.end()) {
        for (auto &callee : itr->second) {
          worklist.push_back(callee);
        }
      }
    }
  }
}

void constructCallGraph(KModule *kmod,
                        map<Function*,set<Function*>> &caller_graph,
                        map<Function*,set<Function*>> &callee_graph) {

  Module *mod = kmod->module;
  for (auto fn_itr = mod->begin(), fn_end = mod->end(); fn_itr != fn_end; ++fn_itr) {
    Function *fn = &*fn_itr;
    if (!fn->isDeclaration() && !fn->isIntrinsic()) {

      for (auto bb_itr = fn->begin(), bb_end = fn->end(); bb_itr != bb_end; ++bb_itr) {
        for (auto in_itr = bb_itr->begin(), in_end = bb_itr->end(); in_itr != in_end; ++in_itr) {
          CallSite CS(cast<Value>(in_itr));
          if (CS) {
            Function *callee = CS.getCalledFunction();
            if (callee != nullptr && !callee->isIntrinsic()) {
              caller_graph[fn].insert(callee);
              callee_graph[callee].insert(fn);
            }
          }
        }
      }
    }
  }
}

void collectEntryFns(const map<string, unsigned> &src, const set<string> &sigs, map<string, unsigned> &entry_points) {

  // potential entry points are common functions reaching a changed function
  for (auto itr = src.begin(), end = src.end(); itr != end; ++itr) {
    // cannot enter at a changed sig
    if (sigs.find(itr->first) == sigs.end()) {

      // update entry point list.  if not present insert, else update to minimum
      const auto &ins = entry_points.insert(make_pair(itr->first, itr->second));
      if (!ins.second) {
        ins.first->second = std::min(ins.first->second, itr->second);
      }
    }
  }
}

void entryFns(KModule *kmod1,
              KModule *kmod2,
              const set<string> &commons,
              const set<string> &sigs,
              const set<string> &bodies,
              map<string, unsigned> &entry_points) {

  set<string> changes;
  changes.insert(bodies.begin(), bodies.end());
  changes.insert(sigs.begin(), sigs.end());

  map<Function*,set<Function*>> caller_graph1;
  map<Function*,set<Function*>> callee_graph1;
  constructCallGraph(kmod1, caller_graph1, callee_graph1);
  map<Function*,set<Function*>> caller_graph2;
  map<Function*,set<Function*>> callee_graph2;
  constructCallGraph(kmod2, caller_graph2, callee_graph2);

  map<string,unsigned> map1;
  reachesFns(kmod1, callee_graph1, commons, changes, map1);

  map<string,unsigned> map2;
  reachesFns(kmod2, callee_graph2, commons, changes, map2);

  // potential entry points are common functions reaching a changed function
  collectEntryFns(map1, sigs, entry_points);

  // though they have common entry points, may need to update distance
  collectEntryFns(map2, sigs, entry_points);
}

void emitDiff(KModule *kmod1, KModule *kmod2, KModule *kmod3, const string &outDir) {

  // kmod3 is optional
  assert(kmod1 && kmod2);

  fs::path path(outDir);
  string pathname = (path /= "diff.json").string();
  ofstream out(pathname, ofstream::out);
  if (out.is_open()) {

    // construct the json object representing the function differences
    Json::Value root = Json::objectValue;
    Json::Value &functions = root["functions"] = Json::objectValue;
    Json::Value &fns_added = functions["added"] = Json::arrayValue;
    Json::Value &fns_removed = functions["removed"] = Json::arrayValue;
    functions["body"] = Json::objectValue;
    functions["signature"] = Json::objectValue;

    set_ex<string> sigs, bodies, commons;
    diffFns(kmod1, kmod2, fns_added, fns_removed, sigs, bodies, commons);

    vector<pair<set_ex<string> *, string>> worklist;
    worklist.emplace_back(make_pair(&bodies, "body"));
    worklist.emplace_back(make_pair(&sigs, "signature"));

    for (const auto &item : worklist) {
      const string &key = item.second;
      for (const auto &fn : *item.first) {
        Json::Value &fn_changed_node = functions[key][fn] = Json::objectValue;
        Json::Value &fn_changed_prev = fn_changed_node["prev"] = Json::arrayValue;
        Json::Value &fn_changed_post = fn_changed_node["post"] = Json::arrayValue;

        set_ex<unsigned> prev_bblocks, post_bblocks;
        findModifiedBlocks(kmod1, kmod2, fn, prev_bblocks, post_bblocks);

        for (auto bb_id : prev_bblocks) {
          fn_changed_prev.append(bb_id);
        }
        for (auto bb_id : post_bblocks) {
          fn_changed_post.append(bb_id);
        }
      }
    }

    // construct the json object representing the global variable differences
    Json::Value &globals = root["globals"] = Json::objectValue;
    Json::Value &gbs_added = globals["added"] = Json::arrayValue;
    Json::Value &gbs_removed = globals["removed"] = Json::arrayValue;
    Json::Value &gbs_changed = globals["changed"] = Json::arrayValue;

    diffGbs(kmod1, kmod2, gbs_added, gbs_removed, gbs_changed);

    // now, record the program entry points reaching changed functions
    Json::Value &fns_entries = root["entryPoints"] = Json::arrayValue;
    map<string, unsigned> entry_points;
    entryFns(kmod1, kmod2, commons, sigs, bodies, entry_points);
    for (const auto &pr : entry_points) {
      Json::Value &entry = fns_entries.append(Json::objectValue);
      entry["function"] = pr.first;
      entry["distance"] = pr.second;
    }

    set_ex<string> names;

    // prev module
    Json::Value &prev_node = root["prev-module"] = Json::objectValue;
    prev_node["name"] = kmod1->getModuleIdentifier();

    Json::Value &prev_exts = prev_node["external"] = Json::arrayValue;
    kmod1->getExternalFunctions(names);
    for (auto &name : names) { prev_exts.append(name); }

    Json::Value &prev_srcs = prev_node["sources"] = Json::arrayValue;
    kmod1->getUserSources(names);
    for (auto &name : names) { prev_srcs.append(name); }

    // then post
    Json::Value &post_node = root["post-module"] = Json::objectValue;
    post_node["name"] = kmod2->getModuleIdentifier();

    Json::Value &post_exts = post_node["external"] = Json::arrayValue;
    kmod2->getExternalFunctions(names);
    for (auto &name : names) { post_exts.append(name); }

    Json::Value &post_srcs = post_node["sources"] = Json::arrayValue;
    kmod2->getUserSources(names);
    for (auto &name : names) { post_srcs.append(name); }

    // finally, the oracle module, if present
    if (kmod3 != nullptr) {
      Json::Value &orcl_node = root["orcl-module"] = Json::objectValue;
      orcl_node["name"] = kmod3->getModuleIdentifier();

      Json::Value &orcl_exts = orcl_node["external"] = Json::arrayValue;
      kmod3->getExternalFunctions(names);
      for (auto &name : names) { orcl_exts.append(name); }

      Json::Value &orcl_srcs = orcl_node["sources"] = Json::arrayValue;
      kmod3->getUserSources(names);
      for (auto &name : names) { orcl_srcs.append(name); }
    }

    string indent;
    if (IndentJson) indent = "  ";

    // write the constructed json object to file
    Json::StreamWriterBuilder builder;
    builder["commentStyle"] = "None";
    builder["indentation"] = indent;
    unique_ptr<Json::StreamWriter> writer(builder.newStreamWriter());
    writer->write(root, &out);
    out << '\n';
  }
}

Module *LoadModule(const string &filename) {

  // Load the bytecode...
  string ErrorMsg;
  auto *ctx = new LLVMContext();
  Module *result = nullptr;
  OwningPtr<MemoryBuffer> BufferPtr;
  llvm::error_code ec=MemoryBuffer::getFileOrSTDIN(filename.c_str(), BufferPtr);
  if (ec) {
    klee_error("error loading program '%s': %s", filename.c_str(), ec.message().c_str());
  }

  result = getLazyBitcodeModule(BufferPtr.get(), *ctx, &ErrorMsg);
  if (result != nullptr) {
    if (result->MaterializeAllPermanently(&ErrorMsg)) {
      delete result;
      result = nullptr;
    }
  }
  if (!result) klee_error("error loading program '%s': %s", filename.c_str(), ErrorMsg.c_str());
  BufferPtr.take();
  return result;
}

KModule *PrepareModule(const string &filename) {

  if (Module *module = LoadModule(filename)) {
    if (!isPrepared(module)) {
      klee_error("not prepared: %s", module->getModuleIdentifier().c_str());
    } else {

      if (KModule *kmodule = new KModule(module)) {
        kmodule->prepare();
        return kmodule;
      }
    }
  }
  return nullptr;
}

int main(int argc, char *argv[]) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseCmdLineArgs(argc, argv);

#ifdef _DEBUG
  EnableMemDebuggingChecks();
#endif // _DEBUG

  int exit_code = 1;
  KModule *kmod1 = PrepareModule(InputFile1);
  if (kmod1 != nullptr) {
    KModule *kmod2 = PrepareModule(InputFile2);
    if (kmod2 != nullptr) {

      // third kmod is optional, and presumed to be a post-instrumented oracle
      KModule *kmod3 = nullptr;
      if (!InputFile3.empty()) {
        kmod3 = PrepareModule(InputFile3);
        if (kmod3->hasOracle()) outs() << kmod3->getModuleIdentifier() << " instrumented with oracle\n";
        else errs() << kmod3->getModuleIdentifier() << " does not contain an oracle\n";
      }

      emitDiff(kmod1, kmod2, kmod3, Output);

      if (kmod3 != nullptr) {
        LLVMContext *ctx = kmod3->getContextPtr();
        delete kmod3;
        delete ctx;
      }

      LLVMContext *ctx = kmod2->getContextPtr();
      delete kmod2;
      delete ctx;
      exit_code = 0;
    }
    LLVMContext *ctx = kmod1->getContextPtr();
    delete kmod1;
    delete ctx;
  }
  return exit_code;
}
