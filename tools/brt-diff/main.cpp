//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Interpreter.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Module/ModuleTypes.h"
#include "klee/Internal/Module/KInstruction.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"
#include "llvm/Analysis/CallGraph.h"

#include <openssl/sha.h>

#include "llvm/Support/system_error.h"
#include "json/json.h"

#include <string>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include <llvm/IR/Intrinsics.h>
#include "klee/util/CommonUtil.h"

#ifdef _DEBUG
#include <gperftools/tcmalloc.h>
#include <gperftools/heap-profiler.h>
#include <gperftools/heap-checker.h>
#endif

using namespace llvm;
using namespace klee;
using namespace std;
namespace alg = boost::algorithm;
namespace fs = boost::filesystem;

namespace {
cl::OptionCategory BrtCategory("specific brt options");
cl::opt<string> InputFile1(cl::desc("<original bytecode>"), cl::Positional);
cl::opt<string> InputFile2(cl::desc("<updated bytecode>"), cl::Positional);
cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::cat(BrtCategory));
cl::opt<bool> Verbose("verbose", cl::init(false), cl::desc("Emit verbose output"), cl::cat(BrtCategory));
cl::opt<string> AssumeEq("assume-equiv", cl::desc("assume the following functions are equivalent (useful for some library routines"), cl::cat(BrtCategory));
cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"), cl::cat(BrtCategory));
cl::opt<bool> ShowArgs("show-args", cl::desc("show invocation command line args"), cl::cat(BrtCategory));
}

//===----------------------------------------------------------------------===//
// main Driver function
//

static void parseArguments(int argc, char **argv) {
  cl::SetVersionPrinter(klee::printVersion);
  cl::ParseCommandLineOptions(argc, argv, " klee\n");
}

uint64_t calcFnHash(Function *fn) {

  HashAccumulator hash;
  vector<const BasicBlock*> worklist;
  set<const BasicBlock*> visited;

  if (!fn->empty()) {
    const BasicBlock *entry = &fn->getEntryBlock();
    worklist.push_back(entry);
    visited.insert(entry);
    while (!worklist.empty()) {
      const BasicBlock *bb = worklist.back();
      worklist.pop_back();

      // add a block header
      hash.add((uint64_t) 0x4df1d4db);
      for (auto &inst : *bb) {
        // add the instruction to the hash
        hash.add((uint64_t) inst.getOpcode());
        for (unsigned idx = 0, end = inst.getNumOperands(); idx != end; ++idx) {
          Value *v = inst.getOperand(idx);
          if (auto c = dyn_cast<Constant>(v)) {

            if (auto ba = dyn_cast<BlockAddress>(c)) {
              (void) ba;
            } else if (auto ci = dyn_cast<ConstantInt>(c)) {
              hash.add(ci->getValue().getZExtValue());
            } else if (auto fp = dyn_cast<ConstantFP>(c)) {
              hash.add(fp->getValueAPF().convertToDouble());
            } else if (auto az = dyn_cast<ConstantAggregateZero>(c)) {
              (void) az;
            } else if (auto ca = dyn_cast<ConstantArray>(c)) {
              (void) ca;
            } else if (auto cs = dyn_cast<ConstantStruct>(c)) {
              (void) cs;
            } else if (auto cv = dyn_cast<ConstantVector>(c)) {
              (void) cv;
            } else if (auto pn = dyn_cast<ConstantPointerNull>(c)) {
              (void) pn;
            } else if (auto ds = dyn_cast<ConstantDataSequential>(c)) {
              (void) ds;
            } else if (auto cx = dyn_cast<llvm::ConstantExpr>(c)) {
              (void) cx;
            } else if (auto uv = dyn_cast<UndefValue>(c)) {
              (void) uv;
            } else if (auto gv = dyn_cast<GlobalValue>(c)) {
              hash.add(gv->getName());
            }
          } else {
          }
        }
      }

      const TerminatorInst *term = bb->getTerminator();
      for (unsigned idx = 0, end = term->getNumSuccessors(); idx != end; ++idx) {
        const BasicBlock *next = term->getSuccessor(idx);
        if (!(visited.insert(next).second))
          continue;
        worklist.push_back(next);
      }
    }
  }
  return hash.get();
}

void diffFns(KModule *kmod1,
             KModule *kmod2,
             const set<string> &assume_eq,
             Json::Value &added,
             Json::Value &removed,
             set<string> &sig,
             set<string> &body,
             set<string> &commons) {

  set<string> fn_names1;
  set<string> fn_names2;

  kmod1->getUserFunctions(fn_names1);
  kmod2->getUserFunctions(fn_names2);

  // find the functions that have been added (in 2 but not in 1)
  set<string> fns_added;
  set_difference(fn_names2.begin(), fn_names2.end(), fn_names1.begin(), fn_names1.end(), inserter(fns_added, fns_added.end()));
  for (auto fn : fns_added) added.append(fn);

  // find the functions that have been removed (in 1 but not in 2)
  set<string> fns_removed;
  set_difference(fn_names1.begin(), fn_names1.end(), fn_names2.begin(), fn_names2.end(), inserter(fns_removed, fns_removed.end()));
  for (auto fn : fns_removed) removed.append(fn);

  // those that are in both will need further checks
  set<string> fns_both;
  set_intersection(fn_names1.begin(), fn_names1.end(), fn_names2.begin(), fn_names2.end(), inserter(fns_both, fns_both.end()));

  Module *mod1 = kmod1->module;
  Module *mod2 = kmod2->module;
  assert(mod1 && mod2);
  vector<pair<Function*,Function*> > fn_pairs;
  fn_pairs.reserve(fns_both.size());
  for (auto fn : fns_both) {
    fn_pairs.emplace_back(make_pair(mod1->getFunction(fn), mod2->getFunction(fn)));
  }

  // check function signatures
  for (const auto &pr : fn_pairs) {
    assert(pr.first && pr.second);

    Function *fn1 = pr.first;
    Function *fn2 = pr.second;
    string fn_name = fn1->getName();

    if (!ModuleTypes::isEquivalentType(fn1->getFunctionType(), fn2->getFunctionType())) {
      sig.insert(fn_name);
    } else if ((assume_eq.find(fn_name) == assume_eq.end()) && (calcFnHash(fn1) != calcFnHash(fn2))) {
      body.insert(fn_name);
    } else {
      commons.insert(fn_name);
    }
  }
}

void diffGbs(KModule *kmod1, KModule *kmod2, Json::Value &added, Json::Value &removed, Json::Value &changed) {

  set<string> gb_names1;
  set<string> gb_names2;

  kmod1->getUserGlobals(gb_names1);
  kmod2->getUserGlobals(gb_names2);

  // find the globals that have been added (in 2 but not in 1)
  set<string> gbs_added;
  set_difference(gb_names2.begin(), gb_names2.end(), gb_names1.begin(), gb_names1.end(), inserter(gbs_added, gbs_added.end()));
  for (auto gb : gbs_added) added.append(gb);

  // find the globals that have been removed (in 1 but not in 2)
  set<string> gbs_removed;
  set_difference(gb_names1.begin(), gb_names1.end(), gb_names2.begin(), gb_names2.end(), inserter(gbs_removed, gbs_removed.end()));
  for (auto gb : gbs_removed) removed.append(gb);

  // those that are in both will need further checks
  set<string> gbs_both;
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
                     const map<Function*,set<Function*>> callee_graph,
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
                const map<Function*,set<Function*> > callee_graph,
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

void emitDiff(KModule *kmod1, KModule *kmod2, const set<string> &assume_eq, const string &outDir) {

  fs::path path(outDir);
  string pathname = (path /= "diff.json").string();
  ofstream out(pathname, ofstream::out);
  if (out.is_open()) {

    // construct the json object representing the function differences
    Json::Value root = Json::objectValue;
    Json::Value &functions = root["functions"] = Json::objectValue;
    Json::Value &fns_added = functions["added"] = Json::arrayValue;
    Json::Value &fns_removed = functions["removed"] = Json::arrayValue;
    Json::Value &fns_changed_sig = functions["signature"] = Json::arrayValue;
    Json::Value &fns_changed_body = functions["body"] = Json::arrayValue;
    Json::Value &fns_equivalent = functions["equivalent"] = Json::arrayValue;

    for (const auto &name : assume_eq) {
      fns_equivalent.append(name);
    }

    set<string> sigs, bodies, commons;
    diffFns(kmod1, kmod2, assume_eq, fns_added, fns_removed, sigs, bodies, commons);
    for (const auto &fn : sigs) fns_changed_sig.append(fn);
    for (const auto &fn : bodies) fns_changed_body.append(fn);

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

    Json::Value &prev_node = root["prev-module"] = Json::objectValue;
    prev_node["name"] = kmod1->getModuleIdentifier();
    Json::Value &prev_ext = prev_node["external"] = Json::arrayValue;
    set<string> names;
    kmod1->getExternalFunctions(names);
    for (auto name : names) {
      prev_ext.append(name);
    }

    Json::Value &prev_srcs = prev_node["sources"] = Json::objectValue;
    kmod1->getUserSources(names);
    for (auto name : names) {
      prev_srcs[name] = Json::objectValue;
    }

    Json::Value &post_node = root["post-module"] = Json::objectValue;
    post_node["name"] = kmod2->getModuleIdentifier();
    Json::Value &post_ext = post_node["external"] = Json::arrayValue;
    kmod2->getExternalFunctions(names);
    for (auto name : names) {
      post_ext.append(name);
    }

    Json::Value &post_srcs = post_node["sources"] = Json::objectValue;
    kmod2->getUserSources(names);
    for (auto name : names) {
      post_srcs[name] = Json::objectValue;
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

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();

  // write out command line info, for reference
  if (ShowArgs) show_args(argc, argv);

#ifdef _DEBUG
  EnableMemDebuggingChecks();
#endif // _DEBUG

  int exit_code = 1;
  KModule *kmod1 = PrepareModule(InputFile1);
  if (kmod1 != nullptr) {
    KModule *kmod2 = PrepareModule(InputFile2);
    if (kmod2 != nullptr) {

      set<string> assume_eq;
      if (!AssumeEq.empty()) {
        boost::split(assume_eq, AssumeEq, boost::is_any_of(","));
      }
      emitDiff(kmod1, kmod2, assume_eq, Output);

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
