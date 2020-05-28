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

  cl::list<string> InputFiles(cl::desc("<original input bytecode>"), cl::Positional, cl::OneOrMore);
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<string> FnPtrPatches("fp-patch", cl::desc("json specification for function pointer patching"), cl::init("fp-patch.json"));
  cl::opt<string> Sources("src", cl::desc("comma delimited list of program source files"));
  cl::opt<bool> Verbose("verbose", cl::init(false), cl::desc("Emit verbose output"));
  cl::opt<TraceType> TraceT("trace",
    cl::desc("Choose the type of trace (default=marked basic blocks"),
    cl::values(clEnumValN(TraceType::none, "none", "do not trace execution"),
               clEnumValN(TraceType::bblocks, "bblk", "trace execution by basic block"),
               clEnumValN(TraceType::statements, "stmt", "trace execution by source statement"),
               clEnumValN(TraceType::assembly, "assm", "trace execution by assembly line"),
               clEnumValEnd),
    cl::init(TraceType::bblocks));

  cl::opt<MarkScope> MarkS("mark",
    cl::desc("Choose the scope for function marking (default=module"),
    cl::values(clEnumValN(MarkScope::none, "none", "do not mark functions"),
    clEnumValN(MarkScope::module, "module", "add IR markers to module functions"),
    clEnumValN(MarkScope::all, "all", "add IR markers to all functions"),
    clEnumValEnd),
    cl::init(MarkScope::module));

  cl::opt<string> AssumeEq("assume-equiv", cl::desc("assume the following functions are equivalent (useful for some library routines"));

#if 0 == 1
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
#endif

  enum LibcType {
    NoLibc, KleeLibc, UcLibc
  };

  cl::opt<LibcType> Libc("libc",
   cl::desc("Choose libc version (none by default)."),
   cl::values(clEnumValN(NoLibc, "none", "Don't link in a libc"),
     clEnumValN(KleeLibc, "klee", "Link in klee libc"),
     clEnumValN(UcLibc, "uclibc", "Link in uclibc (adapted for klee)"),
     clEnumValEnd),
   cl::init(UcLibc));


#if 0 == 1
  cl::opt<bool>
  WithPOSIXRuntime("posix-runtime",
                cl::desc("Link with POSIX runtime.  Options that can be passed as arguments to the programs are: --sym-arg <max-len>  --sym-args <min-argvs> <max-argvs> <max-len> + file model options"),
                cl::init(false));
#endif

  cl::opt<bool> OptimizeModule("optimize", cl::desc("Optimize before execution"), cl::init(false));
  cl::opt<bool> CheckDivZero("check-div-zero", cl::desc("Inject checks for division-by-zero"), cl::init(false));
  cl::opt<bool> CheckOvershift("check-overshift", cl::desc("Inject checks for overshift"), cl::init(false));
  cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"));
  cl::list<string> LinkLibraries("link-llvm-lib", cl::desc("Link the given libraries before execution"), cl::value_desc("library file"));
  cl::opt<bool> ShowArgs("show-args", cl::desc("show invocation command line args"));
}


//===----------------------------------------------------------------------===//
// main Driver function
//

static void parseArguments(int argc, char **argv) {
  cl::SetVersionPrinter(klee::printVersion);
  cl::ParseCommandLineOptions(argc, argv, " klee\n");
}

bool has_inline_asm(const Function *fn) {

  for (const auto &bb : *fn) {
    for (const auto &inst : bb) {
      if (const CallInst *ci = dyn_cast<CallInst>(&inst)) {
        if (isa<InlineAsm>(ci->getCalledValue())) {
          return true;
        }
      }
    }
  }
  return false;
}

void emitGlobalValueWarning(const set<const llvm::Value*> &vals, const string &msg) {

  for (const auto &val: vals) {
    string name = "#unnamed";
    if (val->hasName()) {
      name = val->getName().str();
    }
    outs() << msg << ": " << name << oendl;
  }
}

void externalsAndGlobalsCheck(const Module *m, set<Function*> &undef_fns_out) {

  // get a set of undefined symbols
  set<const Value*> undefined_fns;
  set<const Value*> defined_fns;
  set<const Value*> undefined_gbs;
  set<const Value*> defined_gbs;
  set<const Value*> inline_assm_fns;

  // get a list of functions declared, but not defined
  for (auto itr = m->begin(), end = m->end(); itr != end; ++itr) {
    const Function *fn = *&itr;
    if (fn->isDeclaration() && !fn->use_empty() && fn->getIntrinsicID() == Intrinsic::not_intrinsic) {
      undefined_fns.insert(fn);
    } else {
      defined_fns.insert(fn);
    }

    if (boost::starts_with(fn->getName().str(), "rpl_")) {
      outs() << "possible gnulib replacement: " << fn->getName().str() << oendl;
    }

    if (has_inline_asm(fn)) {
      inline_assm_fns.insert(fn);
    }
  }

  // get a list of globals declared, but not defined
  for (auto itr = m->global_begin(), end = m->global_end(); itr != end; ++itr) {
    if (itr->isDeclaration() && !itr->use_empty()) {
      undefined_gbs.insert(itr);
    } else {
      defined_gbs.insert(itr);
    }
  }

  // if the target of the alias is not defined, then we still have an undefined value.
  for (auto itr = m->alias_begin(), end = m->alias_end(); itr != end; ++itr) {
    const auto aliassee = itr->getAliasee();
    if (const auto fn = dyn_cast<Function>(aliassee)) {
      if (defined_fns.find(fn) == defined_fns.end()) {
        undefined_fns.insert(fn);
      }
    } else if (const auto gv = dyn_cast<GlobalVariable>(aliassee)) {
      if (defined_gbs.find(gv) == defined_gbs.end()) {
        undefined_gbs.insert(gv);
      }
    }
  }

  // the remaining undefined symbols may be handled by various either the SpecialFunctionHandler or SysModel
  // these should be removed from the warning list.
  filterHandledFunctions(undefined_fns);
  filterHandledGlobals(undefined_gbs);

  // insert discovered undefined fns into the output parameter
  for (auto const &val : undefined_fns) {
    if (auto fn = dyn_cast<Function>(val)) {
      undef_fns_out.insert(const_cast<Function*>(fn));
    }
  }

  // report anything found
  if (!undefined_fns.empty())
    emitGlobalValueWarning(undefined_fns, "Undefined function");
  if (!undefined_gbs.empty())
    emitGlobalValueWarning(undefined_gbs, "Undefined global");
  if (!inline_assm_fns.empty())
    emitGlobalValueWarning(inline_assm_fns, "Inline assembly in function");
}

#ifndef SUPPORT_KLEE_UCLIBC
static llvm::Module *linkWithUclibc(llvm::Module *mainModule, StringRef libDir) {
  klee_error("invalid libc, no uclibc support!\n");
}
#else
static void replaceOrRenameFunction(llvm::Module *module,
                const char *old_name, const char *new_name)
{
  Function *f, *f2;
  f = module->getFunction(new_name);
  f2 = module->getFunction(old_name);
  if (f2) {
    if (f) {
      f2->replaceAllUsesWith(f);
      f2->eraseFromParent();
    } else {
      f2->setName(new_name);
      assert(f2->getName() == new_name);
    }
  }
}

static llvm::Module *linkWithUclibc(llvm::Module *mainModule, StringRef libDir) {

  LLVMContext &ctx = mainModule->getContext();
  // Ensure that klee-uclibc exists
  SmallString<128> uclibcBCA(libDir);

  string uclibcLib = "klee-uclibc";
  string extension = ".bca";
  llvm::DataLayout targetData(mainModule);
  Expr::Width width = targetData.getPointerSizeInBits();
  if (width == Expr::Int32) {
    uclibcLib += "-32";
  } else if (width == Expr::Int64) {
    uclibcLib += "-64";
  }
  uclibcLib += extension;
  llvm::sys::path::append(uclibcBCA, uclibcLib);

  bool uclibcExists=false;
  llvm::sys::fs::exists(uclibcBCA.c_str(), uclibcExists);
  if (!uclibcExists)
    klee_error("Cannot find klee-uclibc : %s", uclibcBCA.c_str());

  mainModule->getOrInsertFunction("__uClibc_main", FunctionType::get(Type::getVoidTy(ctx), vector<Type*>(), true));
  mainModule->getOrInsertFunction("setbuf", FunctionType::get(Type::getVoidTy(ctx), vector<Type*>(), true));

  Function *f = mainModule->getFunction("__ctype_get_mb_cur_max");
  if (f) f->setName("_stdlib_mb_cur_max");

  // Strip of asm prefixes for 64 bit versions because they are not
  // present in uclibc and we want to make sure stuff will get
  // linked. In the off chance that both prefixed and unprefixed
  // versions are present in the module, make sure we don't create a
  // naming conflict.
  for (Module::iterator fi = mainModule->begin(), fe = mainModule->end(); fi != fe; ++fi) {
    Function *f = static_cast<Function *>(fi);
    const string &name = f->getName();
    if (name[0]=='\01') {
      unsigned size = name.size();
      if (name[size-2]=='6' && name[size-1]=='4') {
        string unprefixed = name.substr(1);

        // See if the unprefixed version exists.
        if (Function *f2 = mainModule->getFunction(unprefixed)) {
          f->replaceAllUsesWith(f2);
          f->eraseFromParent();
        } else {
          f->setName(unprefixed);
        }
      }
    }
  }

  // must rename iso99 version before linking, otherwise will not pull in new target
  replaceOrRenameFunction(mainModule, "__isoc99_fscanf", "fscanf");

  set<string> retain_fns = { "setbuf" };

  mainModule = klee::linkWithLibrary(mainModule, uclibcBCA.c_str());
  assert(mainModule && "unable to link with uclibc");

  replaceOrRenameFunction(mainModule, "__libc_open", "open");
  replaceOrRenameFunction(mainModule, "__libc_fcntl", "fcntl");

  // Take care of fortified functions
  replaceOrRenameFunction(mainModule, "__fprintf_chk", "fprintf");

  // XXX we need to rearchitect so this can also be used with
  // programs externally linked with uclibc.

  // RLR TODO: evaluate the continuing need for this
  // We now need to swap things so that __uClibc_main is the entry
  // point, in such a way that the arguments are passed to
  // __uClibc_main correctly. We do this by renaming the user main
  // and generating a stub function to call __uClibc_main. There is
  // also an implicit cooperation in that runFunctionAsMain sets up
  // the environment arguments to what uclibc expects (following
  // argv), since it does not explicitly take an envp argument.
//  Function *userMainFn = mainModule->getFunction(UserMain);
//  assert(userMainFn && "unable to get user main");
  Function *uclibcMainFn = mainModule->getFunction("__uClibc_main");
  assert(uclibcMainFn && "unable to get uclibc main");
  assert(uclibcMainFn->getFunctionType()->getNumParams() == 7);

  // modify module for cbert
  modify_clib(mainModule);
  return mainModule;
}
#endif


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

Module *LinkModule(Module *module, const string &libDir) {

  switch (Libc) {
  case NoLibc: /* silence compiler warning */
    break;

    // RLR TODO: uclibc is 64-bit only
  case KleeLibc: {
    // FIXME: Find a reasonable solution for this.
    SmallString<128> Path(libDir);
    llvm::sys::path::append(Path, "klee-libc.bc");
    module = klee::linkWithLibrary(module, Path.c_str());
    assert(module && "unable to link with klee-libc");
    break;
  }

  case UcLibc:
    module = linkWithUclibc(module, libDir);
    break;
  }

#if 0
  if (WithPOSIXRuntime) {
    SmallString<128> Path(LibraryDir);

    string posixLib = "libkleeRuntimePOSIX";
    Module::PointerSize width = module->getPointerSize();
    if (width == Module::PointerSize::Pointer32) {
      posixLib += "-32";
    } else if (width == Module::PointerSize::Pointer64) {
      posixLib += "-64";
    }
    posixLib += ".bca";

    llvm::sys::path::append(Path, posixLib);
    outs() << "NOTE: Using model: " << Path.c_str() << '\n';
    module = klee::linkWithLibrary(module, Path.c_str());
    assert(module && "unable to link with simple model");
  }
#endif

  for (auto itr = LinkLibraries.begin(), end = LinkLibraries.end(); itr != end; ++itr) {
    const char * libFilename = itr->c_str();
    outs() << "Linking in library: " << libFilename << '\n';
    module = klee::linkWithLibrary(module, libFilename);
  }
  return module;
}

void LoadIndirectPatches(const string &filename, IndirectCallRewriteRecs &recs) {

  assert(!filename.empty());
  assert(recs.empty());

  ifstream infile(filename);
  if (infile.is_open()) {
    Json::Value root;
    infile >> root;
    infile.close();

    if (root.isArray()) {
      recs.reserve(root.size());
      for (Json::Value &rec : root) {
        Json::Value &scope = rec["scope"];
        string sig = rec["sig"].asString();
        string target = rec["target"].asString();
        recs.emplace_back(target, sig);

        // now set the scope of the patches
        set<string> &s = recs.back().scope;
        for (Json::Value &e : scope) {
          s.insert(e.asString());
        }
      }
    }
  }
}

KModule *PrepareModule(const string &filename,
                       set<Function*> &undefined_fns,
                       const IndirectCallRewriteRecs &rewrites,
                       const string& libDir,
                       TraceType ttype,
                       MarkScope mscope) {

  if (Module *module = LoadModule(filename)) {

    if (isPrepared(module)) {
      errs() << "already prepared: " << module->getModuleIdentifier() << '\n';
    } else {

      module = dropUnusedFunctions(module);

      set<string> sources;
      if (!Sources.empty()) {
        boost::split(sources, Sources, [](char c){return c == ',';});
      }

      module = rewriteFunctionPointers(module, rewrites);
      module = LinkModule(module, libDir);

      if (KModule *kmodule = new KModule(module)) {

        Interpreter::ModuleOptions MOpts;
        MOpts.LibraryDir = libDir;
        MOpts.Optimize = OptimizeModule;
        MOpts.CheckDivZero = CheckDivZero;
        MOpts.CheckOvershift = CheckOvershift;

        kmodule->transform(MOpts, sources, ttype, mscope);
        externalsAndGlobalsCheck(module, undefined_fns);
        return kmodule;
      }
    }
    delete module;
  }
  return nullptr;
}

bool SaveModule(KModule *kmod, const string &outDir) {

  bool result = false;
  assert(kmod->module != nullptr);
  fs::path path(outDir);
  string pathname = (path /= kmod->getModuleIdentifier()).string();

  string fs_err;
  raw_fd_ostream outFile(pathname.c_str(), fs_err, sys::fs::F_Binary);
  if (fs_err.empty()) {
    outs() << "writing " << pathname << '\n';
    WriteBitcodeToFile(kmod->module, outFile);
    result = true;
  } else {
    outs() << fs_err << '\n';
  }
  return result;
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
             set<string> &common) {

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
      common.insert(fn_name);
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

#if 0

// RLR TODO: restore type comparison

void constructTypeMap(Module *mod, map<string,StructType*> &ty_names) {

  set<Type*> types;
  ModuleTypes mod_types(mod, types);
  for (const auto &ty : types) {
    if (ty->isStructTy()) {
      auto *sty = cast<StructType>(ty);
      if (sty->hasName()) {
        ty_names.insert(make_pair(sty->getName(), sty));
      }
    }
  }
}
#endif

void diffTypes(KModule *kmod1, KModule *kmod2, Json::Value &added, Json::Value &removed, Json::Value &changed) {

  map<string,StructType*> ty_names1;
//  constructTypeMap(kmod1->module, ty_names1);
  set<string> types1;
//  for (const auto &itr : ty_names1) types1.insert(itr.first);

  map<string,StructType*> ty_names2;
//  constructTypeMap(kmod2->module, ty_names2);
  set<string> types2;
//  for (const auto &itr : ty_names2) types2.insert(itr.first);

  set<string> types_added;
  set_difference(types2.begin(), types2.end(), types1.begin(), types1.end(), inserter(types_added, types_added.end()));
  for (auto ty : types_added) added.append(ty);

  // find the globals that have been removed (in 1 but not in 2)
  set<string> types_removed;
  set_difference(types1.begin(), types1.end(), types2.begin(), types2.end(), inserter(types_removed, types_removed.end()));
  for (auto ty : types_removed) removed.append(ty);

  // those that are in both will need further checks
  set<string> types_both;
  set_intersection(types1.begin(), types1.end(), types2.begin(), types2.end(), inserter(types_both, types_both.end()));

  for (const auto &name : types_both) {
    const auto &itr1 = ty_names1.find(name);
    const auto &itr2 = ty_names2.find(name);
    assert(itr1 != ty_names1.end());
    assert(itr2 != ty_names2.end());
    if (!ModuleTypes::isEquivalentType(itr1->second, itr2->second)) {
      changed.append(name);
    }
  }
}

void constructCallGraphs(KModule *kmod,
                         map<Function*,set<Function*> > &caller_graph,
                         map<Function*,set<Function*> > &callee_graph) {

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

void calcDistanceMap(Module *mod,
                     const map<Function*,set<Function*> > callee_graph,
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

void addReaching(Function *fn, const map<Function*,set<Function*> > &caller_graph, set<Function*> &reaching) {

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

void entryFns(KModule *kmod1,
              KModule *kmod2,
              const set<string> &commons,
              const set<string> &sigs,
              const set<string> &bodies,
              const set<Function*> &undefined_fns,
              map<string,pair<unsigned,set<Function*> > > &entry_points) {

  set<string> changes;
  changes.insert(bodies.begin(), bodies.end());
  changes.insert(sigs.begin(), sigs.end());

  map<Function*,set<Function*> > caller_graph1;
  map<Function*,set<Function*> > callee_graph1;
  constructCallGraphs(kmod1, caller_graph1, callee_graph1);
  map<Function*,set<Function*> > caller_graph2;
  map<Function*,set<Function*> > callee_graph2;
  constructCallGraphs(kmod2, caller_graph2, callee_graph2);

  map<string,unsigned> map1;
  reachesFns(kmod1, callee_graph1, commons, changes, map1);

  map<string,unsigned> map2;
  reachesFns(kmod2, callee_graph2, commons, changes, map2);

  // potential entries are those that reach any changed function and functions whose bodies (only) have changed.
  for (auto itr1 = map1.begin(), end1 = map1.end(); itr1 != end1; ++itr1) {
    // cannot enter at a changed sig
    if (sigs.find(itr1->first) == sigs.end()) {
      auto itr2 = map2.find(itr1->first);
      if (itr2 != map2.end()) {
        auto ins = entry_points.insert(make_pair(itr1->first, make_pair(std::min(itr1->second, itr2->second), set<Function*>{})));
        auto &undefines = ins.first->second.second;
        set<Function*> reach;
        addReaching(kmod1->getFunction(itr1->first), caller_graph1, reach);
        addReaching(kmod2->getFunction(itr2->first), caller_graph2, reach);
        set_intersection(undefined_fns.begin(), undefined_fns.end(), reach.begin(), reach.end(), inserter(undefines, undefines.end()));
      }
    }
  }
}

void emitDiff(KModule *kmod1, KModule *kmod2,
              const set<Function*> &undefined_fns,
              const set<string> &assume_eq,
              const string &outDir) {

  fs::path path(outDir);
  string pathname = (path /= "diff.json").string();
  ofstream out(pathname, ofstream::out);
  if (out.is_open()) {

    // construct the json object representing the differences
    Json::Value root = Json::objectValue;
    Json::Value &functions = root["functions"] = Json::objectValue;
    Json::Value &fns_added = functions["added"] = Json::arrayValue;
    Json::Value &fns_removed = functions["removed"] = Json::arrayValue;
    Json::Value &fns_changed_sig = functions["signature"] = Json::arrayValue;
    Json::Value &fns_changed_body = functions["body"] = Json::arrayValue;
    Json::Value &fns_equivalent = functions["equivalent"] = Json::arrayValue;
    Json::Value &fns_undef = functions["undefined"] = Json::arrayValue;
    for (const auto &name : assume_eq) {
      fns_equivalent.append(name);
    }

    set<string> undefined_fn_names;
    for (const auto &fn : undefined_fns) {
      undefined_fn_names.insert(fn->getName().str());
    }
    for (const auto &name : undefined_fn_names) {
      fns_undef.append(name);
    }

    set<string> added, removed, sigs, bodies, commons;
    diffFns(kmod1, kmod2, assume_eq, fns_added, fns_removed, sigs, bodies, commons);
    for (const auto &fn : sigs) fns_changed_sig.append(fn);
    for (const auto &fn : bodies) fns_changed_body.append(fn);

    Json::Value &globals = root["globals"] = Json::objectValue;
    Json::Value &gbs_added = globals["added"] = Json::arrayValue;
    Json::Value &gbs_removed = globals["removed"] = Json::arrayValue;
    Json::Value &gbs_changed = globals["changed"] = Json::arrayValue;
    diffGbs(kmod1, kmod2, gbs_added, gbs_removed, gbs_changed);

#if 0 == 1
    Json::Value &types = root["types"] = Json::objectValue;
    Json::Value &tps_added = types["added"] = Json::arrayValue;
    Json::Value &tps_removed = types["removed"] = Json::arrayValue;
    Json::Value &tps_changed = types["changed"] = Json::arrayValue;
    diffTypes(kmod1, kmod2, tps_added, tps_removed, tps_changed);
#endif

    root["pre-module"] = kmod1->getModuleIdentifier();
    root["post-module"] = kmod2->getModuleIdentifier();

    Json::Value &fns_entries = functions["entryPoints"] = Json::objectValue;
    map<string,pair<unsigned,set<Function*> > > entry_points;
    entryFns(kmod1, kmod2, commons, sigs, bodies, undefined_fns, entry_points);
    for (const auto &pr : entry_points) {
      Json::Value &fn_entry = fns_entries[pr.first] = Json::objectValue;
      fn_entry["distance"] = pr.second.first;
      if (!pr.second.second.empty()) {
        set<string> names;
        for (const auto &fn : pr.second.second) {
          names.insert(fn->getName().str());
        }
        Json::Value &undef_fns = fn_entry["undefinedFns"] = Json::arrayValue;
        for (const auto &name : names) {
          undef_fns.append(name);
        }
      }
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

void emitInfo(const vector<KModule *> &kmods, const string &outDir) {

  fs::path path(outDir);
  string pathname = (path /= "info.json").string();
  ofstream out(pathname, ofstream::out);
  if (out.is_open()) {

    set<string> generated;
    Json::Value root = Json::objectValue;
    for (const auto &kmod : kmods) {
      string md_name = kmod->getModuleIdentifier();
      auto result = generated.insert(md_name);
      if (result.second) {
        Json::Value &module = root[md_name] = Json::objectValue;
        for (auto itr = kmod->functions.begin(), end = kmod->functions.end(); itr != end; ++itr) {
          KFunction *kf = *itr;
          string fn_name = kf->getName();
          const BasicBlock *fn_entry = &kf->function->getEntryBlock();
          unsigned entry = kf->basicBlockEntry[const_cast<BasicBlock *>(fn_entry)];
          KInstruction *kentry = kf->instructions[entry];
          string src_name = kentry->info->path;
          module[fn_name] = src_name;
        }
      }
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

  string libDir = InterpreterHandler::getRunTimeLibraryPath(argv[0]);
  fs::path outPath(Output);
  if (!fs::exists(outPath)) {
    fs::create_directories(outPath);
  }

  IndirectCallRewriteRecs indirect_rewrites;
  if (!FnPtrPatches.empty()) {
    LoadIndirectPatches(FnPtrPatches, indirect_rewrites);
  }

  int exit_code = 0;
  vector<KModule*> kmods;
  kmods.reserve(InputFiles.size());
  set<Function*> undefined_fns;

  for (const string &input_file : InputFiles) {

    if (KModule *kmod = PrepareModule(input_file, undefined_fns, indirect_rewrites, libDir, TraceT, MarkS)) {
      kmods.push_back(kmod);
      if (!SaveModule(kmod, Output)) {
        exit_code = 1;
      }
    }
  }

  if (kmods.size() >= 2) {

    set<string> assume_eq;
    if (!AssumeEq.empty()) {
      boost::split(assume_eq, AssumeEq, boost::is_any_of(","));
    }
    emitDiff(kmods[0], kmods[1], undefined_fns, assume_eq, Output);
  }

  emitInfo(kmods, Output);

  for (auto kmod : kmods) {
    LLVMContext *ctx = kmod->getContextPtr();
    delete kmod;
    delete ctx;
  }
  return exit_code;
}
