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
#include "klee/Statistics.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/System/Memory.h"
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

#include <openssl/sha.h>

#include "llvm/Support/system_error.h"
#include "json/json.h"

#include <dirent.h>
#include <unistd.h>

#include <string>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include <llvm/IR/Intrinsics.h>
#include "klee/util/CommonUtil.h"


using namespace llvm;
using namespace klee;
using namespace std;

namespace {

  cl::opt<string> InputFile1(cl::desc("<original input bytecode>"), cl::Positional, cl::Required);
  cl::opt<string> InputFile2(cl::desc("<modified input bytecode>"), cl::Positional);
  cl::opt<bool> IndentJson("indent-json", cl::desc("indent emitted json for readability"), cl::init(true));
  cl::opt<bool> Verbose("verbose", cl::init(false), cl::desc("Emit verbose output"));
  cl::opt<TraceType>
    TraceT("trace",
      cl::desc("Choose libc version (none by default)."),
      cl::values(clEnumValN(TraceType::none, "none", "do not trace execution"),
                 clEnumValN(TraceType::bblocks, "bblk", "trace execution by basic block"),
                 clEnumValN(TraceType::statements, "stmt", "trace execution by source statement"),
                 clEnumValN(TraceType::assembly, "assm", "trace execution by assembly line"),
                 clEnumValEnd),
      cl::init(TraceType::bblocks));


#if 0 == 1
  cl::opt<bool> WarnAllExternals("warn-all-externals", cl::desc("Give initial warning for all externals."));
#endif

  enum LibcType {
    NoLibc, KleeLibc, UcLibc
  };

  cl::opt<LibcType>
    Libc("libc",
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
}


//===----------------------------------------------------------------------===//
// main Driver function
//


string getRunTimeLibraryPath(const char *argv0) {
  // allow specifying the path to the runtime library
  const char *env = getenv("KLEE_RUNTIME_LIBRARY_PATH");
  if (env) {
    return string(env);
  }

  if (strlen(KLEE_INSTALL_RUNTIME_DIR) > 0) {
    return string(KLEE_INSTALL_RUNTIME_DIR);
  }

  // Take any function from the execution binary but not main (as not allowed by
  // C++ standard)
  void *MainExecAddr = (void *)(intptr_t)getRunTimeLibraryPath;
  SmallString<128> toolRoot(llvm::sys::fs::getMainExecutable(argv0, MainExecAddr));

  // Strip off executable so we have a directory path
  llvm::sys::path::remove_filename(toolRoot);

  SmallString<128> libDir;

  if (strlen( KLEE_INSTALL_BIN_DIR ) != 0 &&
      strlen( KLEE_INSTALL_RUNTIME_DIR ) != 0 &&
      toolRoot.str().endswith( KLEE_INSTALL_BIN_DIR )) {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using installed KLEE library runtime: ");
    libDir = toolRoot.str().substr(0,
               toolRoot.str().size() - strlen( KLEE_INSTALL_BIN_DIR ));
    llvm::sys::path::append(libDir, KLEE_INSTALL_RUNTIME_DIR);
  } else {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() << "Using build directory KLEE library runtime :");
    libDir = KLEE_DIR;
    llvm::sys::path::append(libDir,RUNTIME_CONFIGURATION);
    llvm::sys::path::append(libDir,"lib");
  }

  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() << libDir.c_str() << "\n");
  return libDir.str();
}

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

void externalsAndGlobalsCheck(const Module *m) {

  static set<string> modeledExternals;
  // RLR TODO: check these warnings
//  interpreter->GetModeledExternals(modeledExternals);
  modeledExternals.insert("__dso_handle");

  set<string> undefinedFunctions;
  set<string> undefinedGlobals;

  // get a list of functions declared, but not defined
  for (auto itr = m->begin(), end = m->end(); itr != end; ++itr) {
    const Function *fn = *&itr;
    string name = fn->getName();
    if (fn->isDeclaration() && !fn->use_empty() && fn->getIntrinsicID() == Intrinsic::not_intrinsic) {
      if (modeledExternals.find(name) == modeledExternals.end()) {
        undefinedFunctions.insert(name);
      }
    }

    if (has_inline_asm(fn)) {
      klee_warning("function \"%s\" has inline asm", name.c_str());
    }
  }

  // get a list of globals declared, but not defined
  for (auto itr = m->global_begin(), end = m->global_end(); itr != end; ++itr) {
    if (itr->isDeclaration() && !itr->use_empty()) {
      string name = itr->getName();
      if (modeledExternals.find(name) == modeledExternals.end()) {
        undefinedGlobals.insert(name);
      }
    }
  }

  // and remove aliases (they define the symbol after global
  // initialization)
  for (auto itr = m->alias_begin(), end = m->alias_end(); itr != end; ++itr) {
    string name = itr->getName();
    undefinedFunctions.erase(name);
    undefinedGlobals.erase(name);
  }

  for (auto fn: undefinedFunctions) {
    klee_warning("reference to external function: %s", fn.c_str());
  }
  for (auto global: undefinedGlobals) {
    klee_warning("reference to undefined global: %s", global.c_str());
  }
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

  // RLR TODO: evaluate how much of this we really need
  Function *f;
  // force import of __uClibc_main
  mainModule->getOrInsertFunction("__uClibc_main", FunctionType::get(Type::getVoidTy(ctx), vector<LLVM_TYPE_Q Type*>(), true));

#if 0 == 1
  // force various imports
  if (WithPOSIXRuntime) {
    LLVM_TYPE_Q llvm::Type *i8Ty = Type::getInt8Ty(ctx);
    mainModule->getOrInsertFunction("realpath",
                                    PointerType::getUnqual(i8Ty),
                                    PointerType::getUnqual(i8Ty),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("getutent",
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("__fgetc_unlocked",
                                    Type::getInt32Ty(ctx),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("__fputc_unlocked",
                                    Type::getInt32Ty(ctx),
                                    Type::getInt32Ty(ctx),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
  }
#endif

  f = mainModule->getFunction("__ctype_get_mb_cur_max");
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

  const FunctionType *ft = uclibcMainFn->getFunctionType();
  assert(ft->getNumParams() == 7);

  // modify module for cbert
  modify_clib(mainModule);
  outs() << "NOTE: Linking with klee-uclibc: " << uclibcBCA << '\n';
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

#if 0 == 1
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

KModule *PrepareModule(const string &filename, const string& libDir, TraceType ttype) {

  if (Module *module = LoadModule(filename)) {

    if (isPrepared(module)) {
      errs() << "already prepared" << module->getModuleIdentifier() << '\n';
    } else {

      set<Function*> module_fns;
      set<GlobalVariable*> module_globals;
      enumModuleVisibleDefines(module, module_fns, module_globals);

      module = rewriteFunctionPointers(module, module_fns);
      module = LinkModule(module, libDir);

      if (KModule *kmodule = new KModule(module)) {

        Interpreter::ModuleOptions MOpts;
        MOpts.LibraryDir = libDir;
        MOpts.Optimize = OptimizeModule;
        MOpts.CheckDivZero = CheckDivZero;
        MOpts.CheckOvershift = CheckOvershift;
        MOpts.user_fns = &module_fns;
        MOpts.user_gbs = &module_globals;

        kmodule->transform(MOpts, ttype);
        externalsAndGlobalsCheck(module);
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
  boost::filesystem::path path(outDir);
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

int main(int argc, char **argv, char **envp) {

  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.
  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
  sys::PrintStackTraceOnErrorSignal();

#ifdef _DEBUG
  EnableMemDebuggingChecks();
#endif // _DEBUG

  string libDir = getRunTimeLibraryPath(argv[0]);

  boost::filesystem::path outPath(Output);
  if (!boost::filesystem::exists(outPath)) {
    boost::filesystem::create_directories(outPath);
  }

  int exit_code = 1;
  if (KModule *kmod1 = PrepareModule(InputFile1, libDir, TraceT)) {
    if (SaveModule(kmod1, Output)) {
      if (InputFile2.empty()) {
        // all done
        exit_code = 0;
      } else {
        // now get the modified module
        if (KModule *kmod2 = PrepareModule(InputFile2, libDir, TraceT)) {
          SaveModule(kmod2, Output);
          // two for two
          exit_code = 0;
          delete kmod2;
        }
      }
    }
    delete kmod1;
  }
  return exit_code;
}
