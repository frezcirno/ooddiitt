//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/util/CommonUtil.h"
#include "klee/util/JsonUtil.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/DataLayout.h"
#include <llvm/IR/Intrinsics.h>
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"
#include "llvm/Analysis/CallGraph.h"

#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>

#include <string>

using namespace llvm;
using namespace klee;
using namespace std;
namespace alg = boost::algorithm;
namespace fs = boost::filesystem;

namespace {
cl::OptionCategory BrtCategory("specific brt options");
cl::list<string> InputFiles(cl::desc("<original input bytecode>"), cl::Positional, cl::OneOrMore);
cl::opt<string> FnPtrPatches("fp-patch", cl::desc("json specification for function pointer patching"), cl::cat(BrtCategory));
cl::opt<string> ClangInfo("clang-info", cl::desc("analysis info json file from C source"), cl::cat(BrtCategory));
cl::opt<string> Sources("src", cl::desc("comma delimited list of program source files"), cl::cat(BrtCategory));
cl::opt<bool> Verbose("verbose", cl::init(false), cl::desc("Emit verbose output"), cl::cat(BrtCategory));
cl::opt<TraceType> TraceT("trace",
  cl::desc("Choose the type of trace (default=basic blocks"),
  cl::values(clEnumValN(TraceType::none, "none", "do not trace execution"),
             clEnumValN(TraceType::bblocks, "bblk", "trace execution by basic block"),
             clEnumValN(TraceType::statements, "stmt", "trace execution by source statement"),
             clEnumValN(TraceType::assembly, "assm", "trace execution by assembly line"),
             clEnumValEnd),
  cl::init(TraceType::bblocks),
  cl::cat(BrtCategory));

cl::opt<MarkScope> MarkS("mark",
  cl::desc("Choose the scope for function marking (default=module"),
  cl::values(clEnumValN(MarkScope::none, "none", "do not mark functions"),
             clEnumValN(MarkScope::module, "module", "add IR markers to module functions"),
             clEnumValN(MarkScope::all, "all", "add IR markers to all functions"),
             clEnumValEnd),
  cl::init(MarkScope::module),
  cl::cat(BrtCategory));

#if 0 == 1
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
#endif

  enum LibcType {
    NoLibc, KleeLibc, UcLibc
  };

cl::opt<LibcType> Libc("libc",
   cl::desc("Choose libc version (default=uclibc)"),
   cl::values(clEnumValN(NoLibc, "none", "Don't link in a libc"),
              clEnumValN(KleeLibc, "klee", "Link in klee libc"),
              clEnumValN(UcLibc, "uclibc", "Link in uclibc (adapted for klee)"),
              clEnumValEnd),
   cl::init(UcLibc),
   cl::cat(BrtCategory));

#if 0 == 1
  cl::opt<bool>
  WithPOSIXRuntime("posix-runtime",
                cl::desc("Link with POSIX runtime.  Options that can be passed as arguments to the programs are: --sym-arg <max-len>  --sym-args <min-argvs> <max-argvs> <max-len> + file model options"),
                cl::init(false));
#endif

cl::opt<bool> OptimizeModule("optimize", cl::desc("Optimize before execution"), cl::cat(BrtCategory));
cl::opt<bool> CheckDivZero("check-div-zero", cl::desc("Inject checks for division-by-zero"), cl::cat(BrtCategory));
cl::opt<bool> CheckOvershift("check-overshift", cl::desc("Inject checks for overshift"), cl::cat(BrtCategory));
cl::opt<string> Output("output", cl::desc("directory for output files (created if does not exist)"), cl::init("brt-out-tmp"), cl::cat(BrtCategory));
cl::list<string> LinkLibraries("link-llvm-lib", cl::desc("Link the given libraries before execution"), cl::value_desc("library file"));
cl::opt<string> Locale("locale", cl::desc("locale for execution (default = 'C'"), cl::cat(BrtCategory));
}


//===----------------------------------------------------------------------===//
// main Driver function
//

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

void globalNameCheck(const string &label, const string &name) {

  static set_ex<string> white_list = {};
  static set_ex<string> popular_suffix = { "16", "32", "64" };

  if (!name.empty() && !white_list.contains(name)) {
    if (!alg::starts_with(name, ".str")) {
      auto idx = name.find_last_not_of("0123456789");
      int num_digits = name.size() - idx - 1;
      if (num_digits > 1) {
        string suffix = name.substr(idx + 1);
        if (!popular_suffix.contains(suffix)) {
          errs() << "possible " << label << " rename: " << name << oendl;
        }
      }
    }
  }
}


void externalsAndGlobalsCheck(const KModule *km) {

  const Module *m = km->module;

  // get a set of undefined symbols
  set<const Value*> undefined_fns;
  set<const Value*> defined_fns;
  set<const Value*> undefined_gbs;
  set<const Value*> defined_gbs;
  set<const Value *> inline_assm_fns;

  // scan through function and global variables to check for names that may have resulted
  // from namespece collisions
  for (auto itr = m->begin(), end = m->end(); itr != end; ++itr) {
    globalNameCheck("fn", itr->getName().str());
  }

  for (auto itr = m->global_begin(), end = m->global_end(); itr != end; ++itr) {
    globalNameCheck("gv", itr->getName().str());
  }

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

  // the remaining undefined symbols may be handled by either the SpecialFunctionHandler or SysModel
  // these should be removed from the warning list.
  filterHandledFunctions(undefined_fns);
  filterHandledGlobals(undefined_gbs);

  // report anything found
  for (auto &value : undefined_fns) {
    auto *fn = dyn_cast<const llvm::Function>(value);
    if (fn != nullptr) {
      outs() << "undefined function" << ": " << fn->getName().str();
      if (fn->isVarArg()) outs() << "-> vararg";
      else {
        ostringstream ss;
        unsigned idx = 0;
        for (auto itr = fn->arg_begin(), end = fn->arg_end(); itr != end; ++itr, ++idx) {
          const Argument *arg = itr;
          if (arg->getType()->isPointerTy() && (!km->isConstFnArg(const_cast<llvm::Function*>(fn), idx))) {
            if (!ss.str().empty()) ss << ",";
            ss << idx;
          }
        }
        string output_args = ss.str();
        if (!output_args.empty()) {
          outs() << "-> output args: " << output_args;
        }
      }
      outs() << oendl;
    }
  }

  if (!undefined_gbs.empty())
    emitGlobalValueWarning(undefined_gbs, "undefined global");
  if (!inline_assm_fns.empty())
    emitGlobalValueWarning(inline_assm_fns, "inline assembly in function");
}

#ifndef SUPPORT_KLEE_UCLIBC
static llvm::Module *linkWithUclibc(llvm::Module *mainModule, StringRef libDir) {
  klee_error("invalid libc, no uclibc support!\n");
}
#else
static void replaceOrRenameFunction(llvm::Module *module, const char *old_name, const char *new_name) {
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

static void dropFnBody(llvm::Module *module, const char *name) {
  if (Function *fn = module->getFunction(name)) {
    fn->deleteBody();
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

  // core utils provides its own version of these functions, use uclibc instead
  dropFnBody(mainModule, "asprintf");
  dropFnBody(mainModule, "vfprintf");
  dropFnBody(mainModule, "fseeko");

  // must rename iso99 version before linking, otherwise will not pull in new target
  replaceOrRenameFunction(mainModule, "__isoc99_fscanf", "fscanf");
  replaceOrRenameFunction(mainModule, "__isoc99_sscanf", "sscanf");

  replaceOrRenameFunction(mainModule, "__mempcpy", "mempcpy");

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

void LoadClangInfo(const string &filename, ClangProgInfo &info) {

  assert(!filename.empty());
  assert(info.empty());

  ifstream infile(filename);
  if (infile.is_open()) {
    Json::Value root;
    infile >> root;
    infile.close();

    if (root.isObject()) {

      // first load the function info
      Json::Value &fn_nodes = root["functions"];

      // iterate over all functions in map
      auto fns = fn_nodes.getMemberNames();
      for (auto &name : fns) {
        auto &fn_node = fn_nodes[name];

        // iterate over each parameter to function
        auto &param_list = fn_node["args"];
        unsigned end = param_list.size();
        auto &fn_info = info.addFn(name, end);
        for (unsigned idx = 0; idx < end; ++idx) {

          // param defaults to not-constant, so only set when true
          auto &param_node = param_list[idx];
          if (param_node["isConst"].asBool()) {
            auto &param_info = fn_info.getArg(idx);
            param_info.setConst();
          }
        }
      }
    }
  }
}

KModule *PrepareModule(const string &filename,
                       const IndirectCallRewriteRecs &rewrites,
                       ClangProgInfo &clang_info,
                       const string& libDir,
                       TraceType ttype,
                       MarkScope mscope) {

  if (Module *module = LoadModule(filename)) {

    if (isPrepared(module)) {
      errs() << "already prepared: " << module->getModuleIdentifier() << '\n';
    } else {

      module = rewriteFunctionPointers(module, rewrites);
      module = LinkModule(module, libDir);

      if (KModule *kmodule = new KModule(module)) {

        Interpreter::ModuleOptions MOpts;
        MOpts.LibraryDir = libDir;
        MOpts.Optimize = OptimizeModule;
        MOpts.CheckDivZero = CheckDivZero;
        MOpts.CheckOvershift = CheckOvershift;
        MOpts.ClangInfo = &clang_info;
        MOpts.ttype = ttype;
        MOpts.mscope = mscope;
        if (!Sources.empty()) {
          boost::split(MOpts.sources, Sources, [](char c){return c == ',';});
        }
        MOpts.locale = Locale;
        kmodule->transform(MOpts);
        externalsAndGlobalsCheck(kmodule);
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

int main(int argc, char *argv[]) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseCmdLineArgs(argc, argv);

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

  ClangProgInfo clang_info;
  if (!ClangInfo.empty()) {
    LoadClangInfo(ClangInfo, clang_info);
  }

  int exit_code = 0;

  for (const string &input_file : InputFiles) {

    KModule *kmod = nullptr;

    // if diff_root is empty, then emit the prepared module
    outs() << "preparing module: " << input_file << oendl;
    SetStackTraceContext(input_file);
    if ((kmod = PrepareModule(input_file, indirect_rewrites, clang_info, libDir, TraceT, MarkS))) {

      if (!SaveModule(kmod, Output)) {
        exit_code = 1;
      }
    }

    LLVMContext *ctx = kmod->getContextPtr();
    delete kmod;
    delete ctx;
  }

  return exit_code;
}
