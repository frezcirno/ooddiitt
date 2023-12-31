//===-- ModuleUtil.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//


#include <set>

#include "klee/Config/Version.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "../Core/SpecialFunctionHandler.h"
#include "klee/Internal/System/Memory.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Object/Archive.h"
#include "llvm/Object/ObjectFile.h"
#include "llvm/Object/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Linker.h"
#include "llvm/Assembly/AssemblyAnnotationWriter.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/DebugLoc.h"

#include "klee/Internal/Support/ModuleUtil.h"

#include <map>
#include <set>
#include <string>
#include <llvm/Support/InstIterator.h>
#include <llvm/DIBuilder.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/IR/IRBuilder.h>

using namespace llvm;
using namespace std;

namespace klee {

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
/// Based on GetAllUndefinedSymbols() from LLVM3.2
///
/// GetAllUndefinedSymbols - calculates the set of undefined symbols that still
/// exist in an LLVM module. This is a bit tricky because there may be two
/// symbols with the same name but different LLVM types that will be resolved to
/// each other but aren't currently (thus we need to treat it as resolved).
///
/// Inputs:
///  M - The module in which to find undefined symbols.
///
/// Outputs:
///  UndefinedSymbols - A set of C++ strings containing the name of all
///                     undefined symbols.
///
static void GetAllUndefinedSymbols(Module *M, set<string> &UndefinedSymbols) {
  static const string llvmIntrinsicPrefix = "llvm.";
  set<string> DefinedSymbols;
  UndefinedSymbols.clear();
  KLEE_DEBUG_WITH_TYPE("klee_linker",
                       dbgs() << "*** Computing undefined symbols ***\n");

  for (Module::iterator I = M->begin(), E = M->end(); I != E; ++I)
    if (I->hasName()) {
      if (I->isDeclaration())
        UndefinedSymbols.insert(I->getName());
      else if (!I->hasLocalLinkage()) {
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
        assert(!I->hasDLLImportLinkage() && "Found dllimported non-external symbol!");
#else
        assert(!I->hasDLLImportStorageClass() && "Found dllimported non-external symbol!");
#endif
        DefinedSymbols.insert(I->getName());
      }
    }

  for (Module::global_iterator I = M->global_begin(), E = M->global_end();
       I != E; ++I)
    if (I->hasName()) {
      if (I->isDeclaration())
        UndefinedSymbols.insert(I->getName());
      else if (!I->hasLocalLinkage()) {
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
        assert(!I->hasDLLImportLinkage() && "Found dllimported non-external symbol!");
#else
        assert(!I->hasDLLImportStorageClass() && "Found dllimported non-external symbol!");
#endif
        DefinedSymbols.insert(I->getName());
      }
    }

  for (Module::alias_iterator I = M->alias_begin(), E = M->alias_end();
       I != E; ++I)
    if (I->hasName())
      DefinedSymbols.insert(I->getName());


  // Prune out any defined symbols from the undefined symbols set
  // and other symbols we don't want to treat as an undefined symbol
  vector<string> SymbolsToRemove;
  for (set<string>::iterator I = UndefinedSymbols.begin();
       I != UndefinedSymbols.end(); ++I) {
    if (DefinedSymbols.count(*I)) {
      SymbolsToRemove.push_back(*I);
      continue;
    }

    // Strip out llvm intrinsics
    if ((I->size() >= llvmIntrinsicPrefix.size()) &&
        (I->compare(0, llvmIntrinsicPrefix.size(), llvmIntrinsicPrefix) == 0)) {
      KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "LLVM intrinsic " << *I <<
                                                 " has will be removed from undefined symbols" << "\n");
      SymbolsToRemove.push_back(*I);
      continue;
    }

    // Symbol really is undefined
    KLEE_DEBUG_WITH_TYPE("klee_linker",
                         dbgs() << "Symbol " << *I << " is undefined.\n");
  }

  // Remove KLEE intrinsics from set of undefined symbols
  for (SpecialFunctionHandler::const_iterator sf = SpecialFunctionHandler::begin(),
           se = SpecialFunctionHandler::end(); sf != se; ++sf) {
    if (UndefinedSymbols.find(sf->name) == UndefinedSymbols.end())
      continue;

    SymbolsToRemove.push_back(sf->name);
    KLEE_DEBUG_WITH_TYPE("klee_linker",
                         dbgs() << "KLEE intrinsic " << sf->name <<
                                " has will be removed from undefined symbols" << "\n");
  }

  // Now remove the symbols from undefined set.
  for (size_t i = 0, j = SymbolsToRemove.size(); i < j; ++i)
    UndefinedSymbols.erase(SymbolsToRemove[i]);

  KLEE_DEBUG_WITH_TYPE("klee_linker",
                       dbgs() << "*** Finished computing undefined symbols ***\n");
}

/*!  A helper function for linkBCA() which cleans up
 *   memory allocated by that function.
 */
static void CleanUpLinkBCA(vector<Module *> &archiveModules) {
  for (vector<Module *>::iterator I = archiveModules.begin(), E = archiveModules.end();
       I != E; ++I) {
    delete (*I);
  }
}

/*! A helper function for klee::linkWithLibrary() that links in an archive of bitcode
 *  modules into a composite bitcode module
 *
 *  \param[in] archive Archive of bitcode modules
 *  \param[in,out] composite The bitcode module to link against the archive
 *  \param[out] errorMessage Set to an error message if linking fails
 *
 *  \return True if linking succeeds otherwise false
 */
static bool linkBCA(object::Archive *archive, Module *composite, string &errorMessage) {
  llvm::raw_string_ostream SS(errorMessage);
  vector<Module *> archiveModules;

  // Is this efficient? Could we use StringRef instead?
  set<string> undefinedSymbols;
  GetAllUndefinedSymbols(composite, undefinedSymbols);

  if (undefinedSymbols.size() == 0) {
    // Nothing to do
    KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "No undefined symbols. Not linking anything in!\n");
    return true;
  }

  KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "Loading modules\n");
  // Load all bitcode files in to memory so we can examine their symbols
  for (object::Archive::child_iterator AI = archive->begin_children(),
           AE = archive->end_children(); AI != AE; ++AI) {

    StringRef memberName;
    llvm::error_code ec = AI->getName(memberName);

    if (ec == llvm::errc::success) {
      KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "Loading archive member " << memberName << "\n");
    } else {
      errorMessage = "Archive member does not have a name!\n";
      return false;
    }

    OwningPtr<object::Binary> child;
    ec = AI->getAsBinary(child);
    if (ec != object::object_error::success) {
      // If we can't open as a binary object file its hopefully a bitcode file

      OwningPtr<MemoryBuffer> buff; // Once this is destroyed will Module still be valid??
      Module *Result = 0;

      if (llvm::error_code ec = AI->getMemoryBuffer(buff)) {
        SS << "Failed to get MemoryBuffer: " << ec.message();
        SS.flush();
        return false;
      }

      if (buff) {
        // FIXME: Maybe load bitcode file lazily? Then if we need to link, materialise the module
        Result = ParseBitcodeFile(buff.get(), composite->getContext(), &errorMessage);

        if (!Result) {
          SS << "Loading module failed : " << errorMessage << "\n";
          SS.flush();
          return false;
        }
        archiveModules.push_back(Result);
      } else {
        errorMessage = "Buffer was NULL!";
        return false;
      }

    } else if (child.get()->isObject()) {
      SS << "Object file " << child.get()->getFileName().data() <<
         " in archive is not supported";
      SS.flush();
      return false;
    } else {
      SS << "Loading archive child with error " << ec.message();
      SS.flush();
      return false;
    }

  }

  KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "Loaded " << archiveModules.size() << " modules\n");

  set<string> previouslyUndefinedSymbols;

  // Walk through the modules looking for definitions of undefined symbols
  // if we find a match we should link that module in.
  unsigned int passCounter = 0;
  do {
    unsigned int modulesLoadedOnPass = 0;
    previouslyUndefinedSymbols = undefinedSymbols;

    for (size_t i = 0, j = archiveModules.size(); i < j; ++i) {
      // skip empty archives
      if (archiveModules[i] == 0)
        continue;
      Module *M = archiveModules[i];
      // Look for the undefined symbols in the composite module
      for (set<string>::iterator S = undefinedSymbols.begin(), SE = undefinedSymbols.end();
           S != SE; ++S) {

        // FIXME: We aren't handling weak symbols here!
        // However the algorithm used in LLVM3.2 didn't seem to either
        // so maybe it doesn't matter?

        if (GlobalValue *GV = dyn_cast_or_null<GlobalValue>(M->getValueSymbolTable().lookup(*S))) {
          if (GV->isDeclaration())
            continue; // Not a definition

          KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "Found " << GV->getName() <<
                                                     " in " << M->getModuleIdentifier() << "\n");

          if (Linker::LinkModules(composite, M, Linker::DestroySource, &errorMessage)) {
            // Linking failed
            SS << "Linking archive module with composite failed:" << errorMessage;
            SS.flush();
            CleanUpLinkBCA(archiveModules);
            return false;
          } else {
            // Link succeed, now clean up
            modulesLoadedOnPass++;
            KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "Linking succeeded.\n");

            delete M;
            archiveModules[i] = 0;

            // We need to recompute the undefined symbols in the composite module
            // after linking
            GetAllUndefinedSymbols(composite, undefinedSymbols);

            break; // Look for symbols in next module
          }

        }
      }
    }

    passCounter++;
    KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "Completed " << passCounter <<
                                               " linker passes.\n" << modulesLoadedOnPass <<
                                               " modules loaded on the last pass\n");
  } while (undefinedSymbols != previouslyUndefinedSymbols); // Iterate until we reach a fixed point


  // What's left in archiveModules we don't want to link in so free it
  CleanUpLinkBCA(archiveModules);

  return true;

}
#endif

Module *linkWithLibrary(Module *module, const string &libraryName) {
  KLEE_DEBUG_WITH_TYPE("klee_linker", dbgs() << "Linking file " << libraryName << "\n");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
  if (!sys::fs::exists(libraryName)) {
    klee_error("Link with library %s failed. No such file.",
               libraryName.c_str());
  }

  OwningPtr<MemoryBuffer> Buffer;
  if (llvm::error_code ec = MemoryBuffer::getFile(libraryName, Buffer)) {
    klee_error("Link with library %s failed: %s", libraryName.c_str(),
               ec.message().c_str());
  }

  sys::fs::file_magic magic = sys::fs::identify_magic(Buffer->getBuffer());

  LLVMContext &Context = module->getContext();
  string ErrorMessage;

  if (magic == sys::fs::file_magic::bitcode) {
    Module *Result = 0;
    Result = ParseBitcodeFile(Buffer.get(), Context, &ErrorMessage);

    if (!Result || Linker::LinkModules(module, Result, Linker::DestroySource,
                                       &ErrorMessage))
      klee_error("Link with library %s failed: %s", libraryName.c_str(),
                 ErrorMessage.c_str());

    delete Result;

  } else if (magic == sys::fs::file_magic::archive) {
    OwningPtr<object::Binary> arch;
    if (llvm::error_code ec = object::createBinary(Buffer.take(), arch))
      klee_error("Link with library %s failed: %s", libraryName.c_str(),
                 ec.message().c_str());

    if (object::Archive *a = dyn_cast<object::Archive>(arch.get())) {
      // Handle in helper
      if (!linkBCA(a, module, ErrorMessage))
        klee_error("Link with library %s failed: %s", libraryName.c_str(),
                   ErrorMessage.c_str());
    } else {
      klee_error("Link with library %s failed: Cast to archive failed", libraryName.c_str());
    }

  } else if (magic.is_object()) {
    OwningPtr<object::Binary> obj;
    if (obj.get()->isObject()) {
      klee_warning("Link with library: Object file %s in archive %s found. "
                   "Currently not supported.",
                   obj.get()->getFileName().data(), libraryName.c_str());
    }
  } else {
    klee_error("Link with library %s failed: Unrecognized file type.",
               libraryName.c_str());
  }

  return module;
#else
  Linker linker("klee", module, false);

  llvm::sys::Path libraryPath(libraryName);
  bool native = false;

  if (linker.LinkInFile(libraryPath, native)) {
    klee_error("Linking library %s failed", libraryName.c_str());
  }

  return linker.releaseModule();
#endif
}

Function *getDirectCallTarget(CallSite cs, bool moduleIsFullyLinked) {
  Value *v = cs.getCalledValue();
  bool viaConstantExpr = false;
  // Walk through aliases and bitcasts to try to find
  // the function being called.
  do {
    if (Function *f = dyn_cast<Function>(v)) {
      return f;
    } else if (llvm::GlobalAlias *ga = dyn_cast<GlobalAlias>(v)) {
      if (moduleIsFullyLinked || !(ga->mayBeOverridden())) {
        v = ga->getAliasee();
      } else {
        v = NULL;
      }
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(v)) {
      viaConstantExpr = true;
      v = ce->getOperand(0)->stripPointerCasts();
    } else {
      v = NULL;
    }
  } while (v != NULL);

  // NOTE: This assert may fire, it isn't necessarily a problem and
  // can be disabled, I just wanted to know when and if it happened.
  assert((!viaConstantExpr) &&
      "FIXME: Unresolved direct target for a constant expression");
  return NULL;
}

static bool valueIsOnlyCalled(const Value *v) {
  for (Value::const_use_iterator it = v->use_begin(), ie = v->use_end();
       it != ie; ++it) {
    if (const Instruction *instr = dyn_cast<Instruction>(*it)) {
      if (instr->getOpcode() == 0)
        continue; // XXX function numbering inst

      // Make sure the instruction is a call or invoke.
      CallSite cs(const_cast<Instruction *>(instr));
      if (!cs)
        return false;

      // Make sure that the value is only the target of this call and
      // not an argument.
      if (cs.hasArgument(v))
        return false;
    } else if (const llvm::ConstantExpr *ce =
        dyn_cast<llvm::ConstantExpr>(*it)) {
      if (ce->getOpcode() == Instruction::BitCast)
        if (valueIsOnlyCalled(ce))
          continue;
      return false;
    } else if (const GlobalAlias *ga = dyn_cast<GlobalAlias>(*it)) {
      // XXX what about v is bitcast of aliasee?
      if (v == ga->getAliasee() && !valueIsOnlyCalled(ga))
        return false;
    } else {
      return false;
    }
  }

  return true;
}

bool functionEscapes(const Function *f) {
  return !valueIsOnlyCalled(f);
}

void enumModuleFunctions(Module *m, set<Function *> &fns) {

  for (auto itr = m->begin(), end = m->end(); itr != end; ++itr) {
    Function *fn = itr;
    if (!fn->hasHiddenVisibility() && !fn->isDeclaration()) {
      fns.insert(fn);
    }
  }
}

void enumModuleGlobals(Module *m, set<GlobalVariable *> &gbs) {

  for (auto itr = m->global_begin(), end = m->global_end(); itr != end; ++itr) {
    GlobalVariable *v = itr;

    // no llvm hidden, and unnamed variables
    if (!v->hasHiddenVisibility() && v->hasName() && (v->getName()[0] != '.') && !v->isDeclaration()) {
      gbs.insert(v);
    }
  }
}

void enumModuleVisibleDefines(Module *m, set<Function *> &fns, set<GlobalVariable *> &gbs) {

  enumModuleFunctions(m, fns);
  enumModuleGlobals(m, gbs);
}

Module *rewriteFunctionPointers(Module *m, const IndirectCallRewriteRecs &recs) {

  // construct a map by function of the indirect calls to rewrite
  map<Function *, map<string, Function *> > rewrite_map;
  map<string, Function *> &rewrite_global = rewrite_map[nullptr];
  for (const auto &rec : recs) {
    Function *target = nullptr;
    if (!rec.target.empty()) {
      target = m->getFunction(rec.target);
      // if target is not in this module, then skip to the next record
      if (target == nullptr)
        continue;
    }
    // if target is null, then the empty target was specified
    if (rec.scope.empty()) {
      // empty scope implies this rewrite is of global scope
      rewrite_global.insert(make_pair(rec.sig, target));
    } else {
      for (const auto &name : rec.scope) {
        if (Function *fn = m->getFunction(name)) {
          auto &rewrite_entry = rewrite_map[fn];
          rewrite_entry.insert(make_pair(rec.sig, target));
        }
      }
    }
  }

  // we loop through all functions, blocks, and instructions so that we are able
  // to emit warnings about unpatched indirect function calls
  for (auto itr = m->begin(), end = m->end(); itr != end; ++itr) {
    Function *fn = itr;
    for (auto &bb : *fn) {

#ifdef _DEBUG
      string fn_name = fn->getName();
#endif
      // cannot change instructions while iterating, so just store the changes to be made
      vector<Instruction *> drops;
      vector<pair<Instruction *, Instruction *> > replacements;

      for (auto itr = bb.begin(), end = bb.end(); itr != end; ++itr) {
        if (Instruction *old_inst = &*itr) {
          CallSite cs(&*itr);
          if (cs) {
            if (Value *val = cs.getCalledValue()) {
              val = val->stripPointerCasts();
              if (!isa<Function>(val)) {

                // we found an indirect call.  try to find an in-scope sig for rewriting
                string sig = to_string(val->getType());

                bool rewrite = false;
                Function *target;

                // check for a function scoped rule first
                auto fn_itr = rewrite_map.find(fn);
                if (fn_itr != rewrite_map.end()) {
                  auto sg_itr = fn_itr->second.find(sig);
                  if (sg_itr != fn_itr->second.end()) {

                    // found a function scope rule
                    rewrite = true;
                    target = sg_itr->second;
                  }
                }
                if (!rewrite) {
                  // no matching rule in function scope, check for global rule
                  auto sg_itr = rewrite_global.find(sig);
                  if (sg_itr != rewrite_global.end()) {
                    // found a global run
                    rewrite = true;
                    target = sg_itr->second;
                  }
                }
                if (rewrite) {
                  if (target == nullptr) {
                    outs() << m->getModuleIdentifier() << ": Dropping indirect call in " << fn->getName() << '\n';
                    drops.push_back(old_inst);
                  } else {
                    outs() << m->getModuleIdentifier() << ": Rewriting indirect call in " << fn->getName() << " as direct call to " << target->getName() << '\n';
                    SmallVector<Value *, 8> args(cs.arg_begin(), cs.arg_end());
                    CallInst *new_inst = CallInst::Create(target, args);
                    new_inst->setCallingConv(cs.getCallingConv());
                    replacements.emplace_back(make_pair(old_inst, new_inst));
                  }
                } else {
                  outs() << m->getModuleIdentifier() << ": Info: function pointer (" << sig << ") in " << fn->getName() << '\n';
                }
              }
            }
          }
        }
      }

      for (auto &inst : drops) {
        inst->removeFromParent();
      }

      for (auto &pr : replacements) {
        if (!pr.first->use_empty())
          pr.first->replaceAllUsesWith(pr.second);
        ReplaceInstWithInst(pr.first, pr.second);
      }
    }
  }
  return m;
}

bool isPrepared(Module *m) {
  NamedMDNode *NMD = m->getNamedMetadata("brt-klee.usr-fns");
  return NMD != nullptr;
}

void modify_clib(llvm::Module *module) {

  // find stdio_init and disable buffering
  if (Function *stdio_init = module->getFunction("_stdio_init")) {

    assert(stdio_init->size() == 1);
    BasicBlock &bb = stdio_init->getEntryBlock();
    Instruction *end_inst = bb.getTerminator();
    assert(dyn_cast<ReturnInst>(end_inst));

    GlobalVariable *stdin = module->getGlobalVariable("stdin");
    GlobalVariable *stdout = module->getGlobalVariable("stdout");
    GlobalVariable *stderr = module->getGlobalVariable("stderr");
    Function *setbuf = module->getFunction("setbuf");
    assert(stdin && stdout && stderr && setbuf);

    IRBuilder<> irb(end_inst);

    Type *byteptr_type = Type::getInt8PtrTy(module->getContext());
    Value *null = Constant::getNullValue(byteptr_type);

    Value *v = irb.CreateLoad(stdin);
    irb.CreateCall2(setbuf, v, null);
    v = irb.CreateLoad(stdout);
    irb.CreateCall2(setbuf, v, null);
    v = irb.CreateLoad(stderr);
    irb.CreateCall2(setbuf, v, null);
  }

  // remove the body of __check_one_fd
  // and trivialize functions we will never use
  // RLR TODO: may need to trivialize or capture other functions
  set<string> drop_fns{"isatty", "tcgetattr", "ioctl", "__check_one_fd"};
  for (const auto &name : drop_fns) {
    if (Function *fn = module->getFunction(name)) {
      fn->dropAllReferences();
    }
  }

  set<string> decl_fns{ "exit" };
  for (const auto &name : decl_fns) {
    if (Function *fn = module->getFunction(name)) {
      fn->deleteBody();
    }
  }

  // clean up unused declarations
  set<Function *> unused_decls;
  for (auto itr = module->begin(), end = module->end(); itr != end; ++itr) {
    Function *fn = itr;
    if (fn->isDeclaration() && fn->getNumUses() == 0) {
      unused_decls.insert(fn);
    }
  }

  for (auto fn : unused_decls) {
    fn->eraseFromParent();
  }
}

} // end namespace klee
