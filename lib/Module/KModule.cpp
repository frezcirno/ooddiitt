//===-- KModule.cpp -------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "KModule"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "Passes.h"
#include "MDBuilder.h"

#include "klee/Config/Version.h"
#include "klee/Interpreter.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/System/Memory.h"
#include "klee/Internal/Module/ModuleTypes.h"

#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/CallSite.h"

#include "llvm/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Path.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Metadata.h"
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/DebugInfo.h>

#include <boost/filesystem.hpp>
#include <boost/algorithm/algorithm.hpp>

using namespace llvm;
using namespace klee;
namespace fs=boost::filesystem;
namespace alg=boost::algorithm;

using std::vector;
using std::map;
using std::set;
using std::deque;
using std::string;
using std::pair;
using std::make_pair;

namespace {
  enum SwitchImplType {
    eSwitchTypeSimple,
    eSwitchTypeLLVM,
    eSwitchTypeInternal
  };

  cl::list<string> MergeAtExit("merge-at-exit");
  cl::opt<SwitchImplType>
  SwitchType("switch-type", cl::desc("Select the implementation of switch"),
             cl::values(clEnumValN(eSwitchTypeSimple, "simple", 
                                   "lower to ordered branches"),
                        clEnumValN(eSwitchTypeLLVM, "llvm", 
                                   "lower using LLVM"),
                        clEnumValN(eSwitchTypeInternal, "internal", 
                                   "execute switch internally"),
                        clEnumValEnd),
             cl::init(eSwitchTypeInternal));

  cl::opt<bool> DebugPrintEscapingFunctions("debug-print-escaping-functions", cl::desc("Print functions whose address is taken."));
}

KModule::KModule(Module *_module) 
  : module(_module),
    targetData(new DataLayout(module)),
    kleeMergeFn(nullptr),
    module_types(_module),
    infos(nullptr),
    constantTable(nullptr),
    module_trace(TraceType::invalid),
    is_prev_module(false)
    {}

KModule::~KModule() {

  delete[] constantTable;
  delete infos;
  for (auto it = functions.begin(), ie = functions.end(); it != ie; ++it) delete *it;
  for (auto it=constantMap.begin(), itE=constantMap.end(); it!=itE;++it) delete it->second;
  delete targetData;
  delete module;
}

/***/

namespace llvm {
extern void Optimize(Module *);
}

// what a hack
static Function *getStubFunctionForCtorList(Module *m,
                                            GlobalVariable *gv,
                                            string name) {
  assert(!gv->isDeclaration() && !gv->hasInternalLinkage() &&
         "do not support old LLVM style constructor/destructor lists");

  vector<LLVM_TYPE_Q Type*> nullary;

  Function *fn = Function::Create(FunctionType::get(Type::getVoidTy(m->getContext()),
						    nullary, false),
				  GlobalVariable::InternalLinkage, 
				  name,
                              m);
  BasicBlock *bb = BasicBlock::Create(m->getContext(), "entry", fn);
  
  // From lli:
  // Should be an array of '{ int, void ()* }' structs.  The first value is
  // the init priority, which we ignore.
  ConstantArray *arr = dyn_cast<ConstantArray>(gv->getInitializer());
  if (arr) {
    for (unsigned i=0; i<arr->getNumOperands(); i++) {
      ConstantStruct *cs = cast<ConstantStruct>(arr->getOperand(i));
      assert(cs->getNumOperands()==2 && "unexpected element in ctor initializer list");
      
      Constant *fp = cs->getOperand(1);      
      if (!fp->isNullValue()) {
        if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(fp))
          fp = ce->getOperand(0);

        if (Function *f = dyn_cast<Function>(fp)) {
	  CallInst::Create(f, "", bb);
        } else {
          assert(0 && "unable to get function pointer from ctor initializer list");
        }
      }
    }
  }
  
  ReturnInst::Create(m->getContext(), bb);

  return fn;
}

static void injectStaticConstructorsAndDestructors(Module *m) {
  GlobalVariable *ctors = m->getNamedGlobal("llvm.global_ctors");
  GlobalVariable *dtors = m->getNamedGlobal("llvm.global_dtors");
  
  if (ctors || dtors) {
    Function *mainFn = m->getFunction("main");
    if (!mainFn)
      klee_error("Could not find main() function.");

    if (ctors)
    CallInst::Create(getStubFunctionForCtorList(m, ctors, "klee.ctor_stub"),
		     "", static_cast<Instruction *>(mainFn->begin()->begin()));
    if (dtors) {
      Function *dtorStub = getStubFunctionForCtorList(m, dtors, "klee.dtor_stub");
      for (Function::iterator it = mainFn->begin(), ie = mainFn->end();
           it != ie; ++it) {
        if (isa<ReturnInst>(it->getTerminator()))
	  CallInst::Create(dtorStub, "", it->getTerminator());
      }
    }
  }
}

bool KModule::replaceFunction(Function *old_fn, Function *new_fn) {

  if (old_fn->getFunctionType() == new_fn->getFunctionType()) {
    old_fn->replaceAllUsesWith(new_fn);
    old_fn->eraseFromParent();
    return true;
  }
  return false;
}

bool KModule::removeFnDuplicates(llvm::Function *base) {

  vector<Function *> duplicates;

  // look over all of the functions in module
  for (auto itr = module->begin(), end = module->end(); itr != end; ++itr) {
    Function *fn = itr;

    // find named functions with the same type as fn, other than fn itself
    // collect in a list since cannot remove a function while iterating
    if (fn != base && fn->hasName()) {

      // if the target name is fn name with appended digits, then this is a duplicate.
      // replace target with fn.
      string base_name = base->getName().str();
      string fn_name = fn->getName().str();

      if (alg::starts_with(fn_name, base_name)) {
        string suffix = fn_name.substr(base_name.size());
        if (!suffix.empty()) {
          if (suffix.find_first_not_of("0123456789") == string::npos) {
            duplicates.push_back(fn);
          }
        }
      }
    }
  }

  for (Function *fn : duplicates) {
    replaceFunction(fn, base);
  }

  return !duplicates.empty();
}

Function *KModule::getOrPromoteFnDuplicate(const std::string &name) {

  if (Function *fn = module->getFunction(name)) {
    return fn;
  }

  // look over all of the functions in module
  for (auto itr = module->begin(), end = module->end(); itr != end; ++itr) {
    Function *fn = itr;
    if (fn->hasName()) {

      // if the target name is fn name with appended digits, then this is a duplicate.
      // replace target with fn.
      string fn_name = fn->getName().str();
      if (alg::starts_with(fn_name, name)) {
        string suffix = fn_name.substr(name.size());
        if (!suffix.empty()) {
          if (suffix.find_first_not_of("0123456789") == string::npos) {
            fn->setName(name);
            return fn;
          }
        }
      }
    }
  }
  return nullptr;
}

void KModule::removeKnownFnDuplicates() {

  static std::set_ex<std::string> known_dups = {"gnu_dev_makedev", "mbuiter_multi_next", "xmalloc",
                                                "xcalloc",         "xrealloc",           "bsd_signal"};

  for (const string &name : known_dups) {
    if (Function *fn = getOrPromoteFnDuplicate(name)) {
      removeFnDuplicates(fn);
    }
  }
}

void KModule::dropUnusedFunctions() {

  unsigned num_fns = UINT32_MAX;
  while (num_fns > module->size()) {
    num_fns = module->size();
    for (auto itr = module->begin(), end = module->end(); itr != end; ++itr) {
      Function *fn = itr;
      if (fn->hasName() && (fn->getName() != "main") && !fn->hasAddressTaken() && fn->use_empty()) {
        outs() << "dropping fn: " << fn->getName() << oendl;
        fn->dropAllReferences();
      }
    }
  }
}

void KModule::dropUnusedGlobals() {

  // RLR TODO: this does not work as expected.  result will not link
  static std::set_ex<string> white_list = {"__stdin", "__stdout", "_obstack", "llvm.used"};

  for (auto itr = module->global_begin(), end = module->global_end(); itr != end; ++itr) {
    GlobalVariable *gv = itr;
    if (gv->use_empty()) {
      string name = gv->getName().str();
      if (!white_list.contains(name)) {
        outs() << "empty_use gv: " << gv->getName() << oendl;
        gv->dropAllReferences();
      }
    }
  }
}

void KModule::transform(const Interpreter::ModuleOptions &opts) {

  assert(module != nullptr);

  insertSetlocaleIntoLibcInit(opts.locale);
  removeKnownFnDuplicates();
  dropUnusedFunctions();
//  dropUnusedGlobals();

  DebugInfoFinder finder;
  finder.processModule(*module);
  for (auto itr = finder.subprogram_begin(), end = finder.subprogram_end(); itr != end; ++itr) {
    DISubprogram di_sp(*itr);
    if (Function *fn = di_sp.getFunction()) {
      if (!fn->isDeclaration()) {
        string pathname = di_sp.getFilename();
        string filename = fs::path(pathname).filename().string();
        string vname = fn->getName().str();
        if (!isPossibleLibrarySource(pathname, filename, vname)) {
          if (opts.sources.empty() || opts.sources.contains(filename)) {
            user_fns.insert(fn);
            outs() << "User function: " << vname << oendl;
          }
        }
      }
    }
  }

  // have to find at least one user function
  if (user_fns.empty()) {
    klee_error("No user functions found");
  }

  for (auto itr = finder.global_variable_begin(), end = finder.global_variable_end(); itr != end; ++itr) {
    DIGlobalVariable di_gv(*itr);
    if (GlobalVariable *gv = di_gv.getGlobal()) {
      if (!gv->isDeclaration()) {
        string pathname = di_gv.getFilename();
        string filename = fs::path(pathname).filename().string();
        string vname = gv->getName().str();
        if (!isPossibleLibrarySource(pathname, filename, vname)) {
          if (opts.sources.empty() || opts.sources.contains(filename)) {
            user_gbs.insert(gv);
            outs() << "User global variable: " << vname;
            if (gv->isConstant()) outs() << " [constant]";
            outs() << oendl;
          }
        }
      }
    }
  }

  set<Function*> fns_to_mark;
  for (auto itr = module->begin(), end = module->end(); itr != end; ++itr) {
    Function *fn = itr;
    if (opts.mscope == MarkScope::all || user_fns.contains(fn)) {
      fns_to_mark.insert(fn);
    }
  }

  LLVMContext &ctx = module->getContext();

  if (!MergeAtExit.empty()) {
    Function *mergeFn = module->getFunction("klee_merge");
    if (!mergeFn) {
      LLVM_TYPE_Q llvm::FunctionType *Ty = 
        FunctionType::get(Type::getVoidTy(ctx),
                          std::vector<LLVM_TYPE_Q Type*>(), false);
      mergeFn = Function::Create(Ty, GlobalVariable::ExternalLinkage,
				 "klee_merge",
				 module);
    }

    for (cl::list<std::string>::iterator it = MergeAtExit.begin(), 
           ie = MergeAtExit.end(); it != ie; ++it) {
      std::string &name = *it;
      Function *f = module->getFunction(name);
      if (!f) {
        klee_error("cannot insert merge-at-exit for: %s (cannot find)",
                   name.c_str());
      } else if (f->isDeclaration()) {
        klee_error("cannot insert merge-at-exit for: %s (external)",
                   name.c_str());
      }

      BasicBlock *exit = BasicBlock::Create(ctx, "exit", f);
      PHINode *result = 0;
      if (f->getReturnType() != Type::getVoidTy(ctx))
        result = PHINode::Create(f->getReturnType(), 0, "retval", exit);
      CallInst::Create(mergeFn, "", exit);
      ReturnInst::Create(ctx, result, exit);

      llvm::errs() << "KLEE: adding klee_merge at exit of: " << name << "\n";
      for (llvm::Function::iterator bbit = f->begin(), bbie = f->end(); 
           bbit != bbie; ++bbit) {
	BasicBlock *bb = static_cast<BasicBlock *>(bbit);
        if (bb != exit) {
          Instruction *i = bbit->getTerminator();
          if (i->getOpcode()==Instruction::Ret) {
            if (result) {
              result->addIncoming(i->getOperand(0), bb);
            }
            i->eraseFromParent();
	    BranchInst::Create(exit, bb);
          }
        }
      }
    }
  }

  // Inject checks prior to optimization... we also perform the
  // invariant transformations that we will end up doing later so that
  // optimize is seeing what is as close as possible to the final
  // module.
  {
    PassManager pm;
    pm.add(new RaiseAsmPass());
    if (opts.CheckDivZero) {
      pm.add(new DivCheckPass());
    }
    if (opts.CheckOvershift) {
      pm.add(new OvershiftCheckPass());
    }
    // FIXME: This false here is to work around a bug in
    // IntrinsicLowering which caches values which may eventually be
    // deleted (via RAUW). This can be removed once LLVM fixes this
    // issue.
    pm.add(new IntrinsicCleanerPass(*targetData, false));
    pm.run(*module);
  }

  if (opts.Optimize) Optimize(module);

  SmallString<128> LibPath(opts.LibraryDir);
  string intrinsicLib = "kleeRuntimeIntrinsic";
  Expr::Width width = targetData->getPointerSizeInBits();

  if (width == Expr::Int32) {
    intrinsicLib += "-32";
  } else if (width == Expr::Int64) {
    intrinsicLib += "-64";
  }

  intrinsicLib += ".bc";
  llvm::sys::path::append(LibPath, intrinsicLib);
  module = linkWithLibrary(module, LibPath.str());

  // Needs to happen after linking (since ctors/dtors can be modified)
  // and optimization (since global optimization can rewrite lists).
  injectStaticConstructorsAndDestructors(module);

  // Finally, run the passes that maintain invariants we expect during
  // interpretation. We run the intrinsic cleaner just in case we
  // linked in something with intrinsics but any external calls are
  // going to be unresolved. We really need to handle the intrinsics
  // directly I think?

  {
    PassManager pm;
    pm.add(createCFGSimplificationPass());
    pm.add(createLoopSimplifyPass());

    switch (SwitchType) {
    case eSwitchTypeInternal: break;
    case eSwitchTypeSimple: pm.add(new LowerSwitchPass());
      break;
    case eSwitchTypeLLVM: pm.add(createLowerSwitchPass());
      break;
    default: klee_error("invalid --switch-type");
    }

    pm.add(createLowerAtomicPass());
    pm.add(new IntrinsicCleanerPass(*targetData));
    pm.add(new PhiCleanerPass());
    pm.add(new InstructionOperandTypeCheckPass());
    if (!fns_to_mark.empty()) {
      pm.add(new FnMarkerPass(mapFnMarkers, mapBBMarkers, fns_to_mark));
    }
    pm.add(new StructFoldPass());
    pm.run(*module);
  }

  /* Build shadow structures */
  infos = new InstructionInfoTable();
  infos->BuildTable(module);

  set<const llvm::Value *> potential_externs;

  /* Build shadow structures */
  for (auto it = module->begin(), ie = module->end(); it != ie; ++it) {
    Function *fn = static_cast<Function *>(it);

    // insert type for later lookup
    mapFnTypes[fn->getFunctionType()].insert(fn);

    if (fn->getIntrinsicID() != Intrinsic::not_intrinsic) {
      addInternalFunction(fn);
    }

    // store clang info for constant function arguments (both internal and external)
    if (auto fn_info = opts.ClangInfo->getFn(fn->getName())) {
      for (unsigned idx = 0; idx < fn_info->arg_size(); ++idx) {
        if (fn_info->getArg(idx).isConst()) {
          fn_const_params[fn].insert(idx);
        }
      }
    }

    if (fn->isDeclaration()) {
      // this could be an external function
      if (!fn->use_empty() && fn->getIntrinsicID() == Intrinsic::not_intrinsic) {
        potential_externs.insert(fn);
      }
    } else {

      KFunction *kf = new KFunction(fn, user_fns.contains(fn), this);

      for (unsigned i = 0; i < kf->numInstructions; ++i) {
        KInstruction *ki = kf->instructions[i];
        ki->info = &infos->getInfo(ki->inst);
        if (i == 0) {
          kf->src_location = (fs::path(ki->info->dir) / fs::path(ki->info->file)).string();
        }
      }
      functions.push_back(kf);
      functionMap.insert(make_pair(fn, kf));
    }
  }

  filterHandledFunctions(potential_externs);
  for (const Value *v : potential_externs) {
    if (const Function *fn = dyn_cast<const Function>(v)) {
      externalFunctions.insert(fn);
    }
  }

  for (auto itr = module->global_begin(), end = module->global_end(); itr != end; ++itr) {
    GlobalVariable *v = itr;
    if (v->hasName()) {
      string name = v->getName();
      if (!name.empty()) {
        mapGlobalVars.insert(make_pair(name, v));
      }
    }
  }

  // store analysis data as llvm metadata
  MDBuilder md_builder(ctx);

  if (!user_fns.empty()) {
    NamedMDNode *NMD = module->getOrInsertNamedMetadata("brt-klee.usr-fns");
    MDNode *node = md_builder.create(user_fns);
    NMD->addOperand(node);
  }

  if (!user_gbs.empty()) {
    NamedMDNode *NMD = module->getOrInsertNamedMetadata("brt-klee.usr-gbs");
    MDNode *node = md_builder.create(user_gbs);
    NMD->addOperand(node);
  }

  if (opts.ttype != TraceType::invalid) {
    NamedMDNode *NMD = module->getOrInsertNamedMetadata("brt-klee.trace-type");
    MDNode *node = md_builder.create((unsigned) opts.ttype);
    NMD->addOperand(node);
  }

  if (!fn_const_params.empty()) {
    NamedMDNode *NMD = module->getOrInsertNamedMetadata("brt-klee.fn-const-args");
    for (auto &itr : fn_const_params) {
      MDNode *node = md_builder.create(itr.first, itr.second);
      NMD->addOperand(node);
    }
  }

  if (!externalFunctions.empty()) {
    NamedMDNode *NMD = module->getOrInsertNamedMetadata("brt-klee.external-fns");
    MDNode *node = md_builder.create(externalFunctions);
    NMD->addOperand(node);
  }

}

void KModule::prepare() {

  if (Function *exit = module->getFunction("exit")) {
    exit->deleteBody();
  }

  // module has already been transformed, need to retrieve prepared values

  // since markers are already assigned, need to retrieve them from the module
  unsigned mdkind_fnID = module->getMDKindID("brt-klee.fnID");
  unsigned mdkind_bbID = module->getMDKindID("brt-klee.bbID");

  for (auto md_itr = module->begin(), md_end = module->end(); md_itr != md_end; ++md_itr) {
    Function *fn = md_itr;
    for (auto fn_itr = fn->begin(), fn_end = fn->end(); fn_itr != fn_end; ++fn_itr) {
      BasicBlock *bb = fn_itr;
      for (auto bb_itr = bb->begin(), bb_end = bb->end(); bb_itr != bb_end; ++bb_itr) {
        Instruction *inst = bb_itr;
        if (MDNode *node = inst->getMetadata(mdkind_fnID)) {
          if (ConstantInt *vi = dyn_cast<ConstantInt>(node->getOperand(0))) {
            mapFnMarkers[fn] = vi->getZExtValue();
          }
        }
        if (MDNode *node = inst->getMetadata(mdkind_bbID)) {
          if (ConstantInt *vi = dyn_cast<ConstantInt>(node->getOperand(0))) {
            mapBBMarkers[bb] = vi->getZExtValue();
          }
        }
      }
    }
  }

  // read out the user defined functions from metadata
  auto node = module->getNamedMetadata("brt-klee.usr-fns");
  if (node != nullptr && node->getNumOperands() > 0) {
    if (auto md = node->getOperand(0)) {
      for (unsigned idx = 0, end = md->getNumOperands(); idx < end; ++idx) {
        if (Value *v = md->getOperand(idx)) {
          if (Function *fn = dyn_cast<Function>(v)) {
            user_fns.insert(fn);
          }
        }
      }
    }
  }

  // and now the globals
  node = module->getNamedMetadata("brt-klee.usr-gbs");
  if (node != nullptr && node->getNumOperands() > 0) {
    if (auto md = node->getOperand(0)) {
      for (unsigned idx = 0, end = md->getNumOperands(); idx < end; ++idx) {
        if (Value *v = md->getOperand(idx)) {
          if (GlobalVariable *gb = dyn_cast<GlobalVariable>(v)) {
            user_gbs.insert(gb);
          }
        }
      }
    }
  }

  // check to see if a default trace type is set in the module
  node = module->getNamedMetadata("brt-klee.trace-type");
  if (node != nullptr && node->getNumOperands() > 0) {
    if (auto md = node->getOperand(0)) {
      if (Value *v = md->getOperand(0)) {
        if (ConstantInt *i = dyn_cast<ConstantInt>(v)) {
          module_trace = (TraceType)i->getZExtValue();
        }
      }
    }
  }

  // read out the external functions from metadata
  node = module->getNamedMetadata("brt-klee.external-fns");
  if (node != nullptr && node->getNumOperands() > 0) {
    if (auto md = node->getOperand(0)) {
      for (unsigned idx = 0, end = md->getNumOperands(); idx < end; ++idx) {
        if (Value *v = md->getOperand(idx)) {
          if (Function *fn = dyn_cast<Function>(v)) {
            externalFunctions.insert(fn);
          }
        }
      }
    }
  }

  // finally, read out the map of function const arguments.
  node = module->getNamedMetadata("brt-klee.fn-const-args");
  if (node != nullptr) {
    for (unsigned fn_idx = 0, fn_end = node->getNumOperands(); fn_idx < fn_end; ++fn_idx) {
      if (auto md = node->getOperand(fn_idx)) {
        if (Function *fn = dyn_cast<Function>(md->getOperand((0)))) {
          auto &s = fn_const_params[fn];
          for (unsigned arg_idx = 1, arg_end = md->getNumOperands(); arg_idx < arg_end; ++arg_idx) {
            ConstantInt *i = dyn_cast<ConstantInt>(md->getOperand(arg_idx));
            s.insert(i->getZExtValue());
          }
        }
      }
    }
  }

  kleeMergeFn = module->getFunction("klee_merge");

  /* Build shadow structures */
  infos = new InstructionInfoTable();
  infos->LoadTable(module);

  /* Build shadow structures */
  for (auto it = module->begin(), ie = module->end(); it != ie; ++it) {

    Function *fn = static_cast<Function *>(it);

    // insert type for later lookup
    mapFnTypes[fn->getFunctionType()].insert(fn);

    if (fn->getIntrinsicID() != Intrinsic::not_intrinsic) {
      addInternalFunction(fn);
    }

    if (fn->isDeclaration()) {

    } else {

      KFunction *kf = new KFunction(fn, user_fns.contains(fn), this);

      for (unsigned i = 0; i < kf->numInstructions; ++i) {
        KInstruction *ki = kf->instructions[i];
        ki->info = &infos->getInfo(ki->inst);
        if (i == 0) {
          kf->src_location = (fs::path(ki->info->dir) / fs::path(ki->info->file)).string();
        }
      }

      functions.push_back(kf);
      functionMap.insert(make_pair(fn, kf));
    }
  }

  for (auto itr = module->global_begin(), end = module->global_end(); itr != end; ++itr) {
    GlobalVariable *v = itr;
    if (v->hasName()) {
      string name = v->getName();
      if (!name.empty()) {
        mapGlobalVars.insert(make_pair(name, v));
      }
    }
  }

  /* Compute various interesting properties */

  for (auto it = functions.begin(), ie = functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    if (functionEscapes(kf->function))
      escapingFunctions.insert(kf->function);
  }

  if (DebugPrintEscapingFunctions && !escapingFunctions.empty()) {
    llvm::errs() << "KLEE: escaping functions: [";
    for (auto it = escapingFunctions.begin(), ie = escapingFunctions.end(); it != ie; ++it) {
      llvm::errs() << (*it)->getName() << ", ";
    }
    llvm::errs() << "]\n";
  }
}

void KModule::insertSetlocaleIntoLibcInit(const string &name) {

  // ensure that setlocale, _locale_init and __uClibc_init are defined in this module
  Function *setlocale = module->getFunction("setlocale");
  if (setlocale == nullptr) return;

  Function *locale_init = module->getFunction("_locale_init");
  if (locale_init == nullptr) return;

  Function *uclibc_init = module->getFunction("__uClibc_init");
  if (uclibc_init == nullptr) return;

  // find the call to _locale_init()
  for (BasicBlock &bb : *uclibc_init) {
    for (Instruction &inst : bb) {
      if (auto ci = dyn_cast<CallInst>(&inst)) {
        if (ci->getCalledFunction() == locale_init) {

          // insert a global variable and call to setlocale
          // 2nd param pting to empty string causes an environment check for locale name
          bool insert_call = true;
          string locale_name = name;
          if (locale_name.empty()) {
            insert_call = false;
            locale_name = "C";
          }
          IRBuilder<> irb(inst.getNextNode());
          GlobalVariable *gv = dyn_cast<GlobalVariable>(irb.CreateGlobalString(locale_name, "__brt_klee_setlocale_name"));
          gv->setConstant(true);
          if (insert_call) {
            SmallVector<Value *, 4> args;
            args.push_back(irb.getInt32(6));
            args.push_back(gv);
            irb.CreateCall(setlocale, args);
          }
          return;
        }
      }
    }
  }
}

void KModule::getUserSources(std::set_ex<std::string> &srcs) const {

  srcs.clear();
  for (auto itr = user_fns.begin(), end = user_fns.end(); itr != end; ++itr) {
    Function *fn = (Function *) *itr;
    if (KFunction *kf = getKFunction(fn)) {
      if (!kf->src_location.empty()) {
        srcs.insert(kf->src_location);
      }
    }
  }
}

void KModule::addTargetedBBlocks(const KFunction *kf, const std::set_ex<unsigned> &bblocks) {

  Function *fn = kf->function;
  for (auto itr = fn->begin(), end = fn->end(); itr != end; ++itr) {
    BasicBlock *bb = itr;
    if (bblocks.contains(getBBlockID(bb))) {
      targeted_bblocks.insert(bb);
    }
  }
}

void KModule::getTargetedFns(std::set_ex<KFunction *> &kfns) const {

  for (BasicBlock *bb : targeted_bblocks) {
    KFunction *kf = getKFunction(bb->getParent());
    if (kf != nullptr) {
      kfns.insert(kf);
    }
  }
}

void KModule::getTargetedFns(std::set_ex<llvm::Function *> &fns) const {
  for (BasicBlock *bb : targeted_bblocks) {
    fns.insert(bb->getParent());
  }
}

Function *KModule::getTargetFunction(Value *value) const {

  Constant *c = dyn_cast<Constant>(value);

  while (c != nullptr) {

    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      return dyn_cast<Function>(gv);
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode() == Instruction::BitCast) {
        c = ce->getOperand(0);
      } else {
        return nullptr;
      }
    }
  }
  return nullptr;
}

KConstant* KModule::getKConstant(Constant *c) {
  map<llvm::Constant*, KConstant*>::iterator it = constantMap.find(c);
  if (it != constantMap.end())
    return it->second;
  return nullptr;
}

unsigned KModule::getConstantID(Constant *c, KInstruction* ki) {
  KConstant *kc = getKConstant(c);
  if (kc)
    return kc->id;

  unsigned id = constants.size();
  kc = new KConstant(c, id, ki);
  constantMap.insert(make_pair(c, kc));
  constants.push_back(c);
  return id;
}

unsigned KModule::getFnID(const llvm::Function *fn) const {

  const auto itr_fn = mapFnMarkers.find(fn);
  if (itr_fn != mapFnMarkers.end()) {
    return itr_fn->second;
  }
  return 0;
}

unsigned KModule::getBBlockID(const llvm::BasicBlock *bb) const {

  const auto itr_bb = mapBBMarkers.find(bb);
  if (itr_bb != mapBBMarkers.end()) {
    return itr_bb->second;
  }
  return 0;
}

void KModule::constructCallGraphs(std::map<llvm::Function *, std::set_ex<llvm::Function *>> *caller_graph,
                                  std::map<llvm::Function *, std::set_ex<llvm::Function *>> *callee_graph) const {

  for (auto fn_itr = module->begin(), fn_end = module->end(); fn_itr != fn_end; ++fn_itr) {
    Function *fn = &*fn_itr;
    if (!fn->isDeclaration() && !fn->isIntrinsic()) {

      for (auto bb_itr = fn->begin(), bb_end = fn->end(); bb_itr != bb_end; ++bb_itr) {
        for (auto in_itr = bb_itr->begin(), in_end = bb_itr->end(); in_itr != in_end; ++in_itr) {
          CallSite CS(cast<Value>(in_itr));
          if (CS) {
            Function *callee = CS.getCalledFunction();
            if (callee != nullptr && !callee->isIntrinsic()) {
              if (caller_graph != nullptr) (*caller_graph)[fn].insert(callee);
              if (callee_graph != nullptr) (*callee_graph)[callee].insert(fn);
            }
          }
        }
      }
    }
  }
}

bool KModule::getTargetDomain(llvm::Function *entry, std::set_ex<llvm::Function *> &dom) const {

  dom.clear();
  std::set_ex<Function *> targeted_fns;
  getTargetedFns(targeted_fns);
  if (targeted_fns.empty()) {
    return false;
  }

  // get a call graph
  std::map<Function *, std::set_ex<Function *>> call_graph;
  constructCallGraph(&call_graph);

  // do a dfs on call graph from entry node to find all simple paths to a targeted fn
  std::vector<Function *> path;
  getTargetDomainDFS(entry, path, call_graph, targeted_fns, dom);
  return true;
}

void KModule::getTargetDomainDFS(Function *fn, std::vector<llvm::Function *> &path,
                                 const std::map<llvm::Function *, std::set_ex<llvm::Function *>> &cg,
                                 const std::set_ex<llvm::Function *> &targets, std::set_ex<llvm::Function *> &dom) const {

  path.push_back(fn);
  if (targets.contains(fn)) {
    for (auto &item : path) dom.insert(item);
  }
  const auto &itr = cg.find(fn);
  if (itr != cg.end()) {
    const auto &children = itr->second;
    for (auto &child : children) {
      if (std::find(path.begin(), path.end(), child) == path.end()) {
        getTargetDomainDFS(child, path, cg, targets, dom);
      }
    }
  }
  path.pop_back();
}

pair<unsigned,unsigned> KModule::getMarker(const llvm::Function *fn, const llvm::BasicBlock *bb) {

  return make_pair(getFnID(fn), getBBlockID(bb));
}

/***/

KConstant::KConstant(llvm::Constant* _ct, unsigned _id, KInstruction* _ki) {
  ct = _ct;
  id = _id;
  ki = _ki;
}

/***/

static int getOperandNum(Value *v,
                         map<Instruction*, unsigned> &registerMap,
                         KModule *km,
                         KInstruction *ki) {
  if (Instruction *inst = dyn_cast<Instruction>(v)) {
    return registerMap[inst];
  } else if (Argument *a = dyn_cast<Argument>(v)) {
    return a->getArgNo();
  } else if (isa<BasicBlock>(v) || isa<InlineAsm>(v) ||
             isa<MDNode>(v)) {
    return -1;
  } else {
    assert(isa<Constant>(v));
    Constant *c = cast<Constant>(v);
    return -(km->getConstantID(c, ki) + 2);
  }
}

std::set_ex<std::string> KFunction::assertionFns{ "__assert_fail", "_serverAssert", "_serverAssertWithInfo", "_serverPanic"};

KFunction::KFunction(llvm::Function *_function, bool user_fn, KModule *km)
  : function(_function),
    numArgs((unsigned) function->arg_size()),
    numInstructions(0),
    trackCoverage(true),
    fn_name(_function->getName().str()),
    is_user(false),
    fnID(0),
    diff_added(false),
    diff_removed(false),
    diff_body(false),
    diff_sig(false),
    fn_hash(0) {

  is_user = user_fn;
  fnID = km->getFnID(function);

  for (auto bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit) {
    BasicBlock *bb = static_cast<BasicBlock *>(bbit);
    basicBlockEntry[bb] = numInstructions;
    numInstructions += bb->size();
  }

  instructions = new KInstruction*[numInstructions];

  map<Instruction*, unsigned> registerMap;

  // The first arg_size() registers are reserved for formals.
  unsigned rnum = numArgs;
  for (auto bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit) {
    for (auto it = bbit->begin(), ie = bbit->end(); it != ie; ++it)
      registerMap[static_cast<Instruction *>(it)] = rnum++;
  }
  numRegisters = rnum;

  unsigned i = 0;
  for (auto bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit) {
    for (auto it = bbit->begin(), ie = bbit->end(); it != ie; ++it) {
      KInstruction *ki;

      switch(it->getOpcode()) {
      case Instruction::GetElementPtr:
      case Instruction::InsertValue:
      case Instruction::ExtractValue:
        ki = new KGEPInstruction(); break;
      default:
        ki = new KInstruction(); break;
      }

      Instruction *inst = static_cast<Instruction *>(it);
      ki->inst = inst;
      ki->dest = registerMap[inst];

      if (isa<CallInst>(it) || isa<InvokeInst>(it)) {
        CallSite cs(inst);
        unsigned numArgs = cs.arg_size();
        ki->operands = new int[numArgs+1];
        ki->operands[0] = getOperandNum(cs.getCalledValue(), registerMap, km,
                                        ki);
        for (unsigned j=0; j<numArgs; j++) {
          Value *v = cs.getArgument(j);
          ki->operands[j+1] = getOperandNum(v, registerMap, km, ki);
        }
      } else {
        unsigned numOperands = it->getNumOperands();
        ki->operands = new int[numOperands];
        for (unsigned j=0; j<numOperands; j++) {
          Value *v = it->getOperand(j);
          ki->operands[j] = getOperandNum(v, registerMap, km, ki);
        }
      }

      instructions[i++] = ki;
    }
  }

  // generate loop information for this fn
  domTree.runOnFunction(*function);
  kloop.releaseMemory();
  kloop.Analyze(domTree.getBase());

  // the right way to do this is to enumerate the loops.
  // but toplevelloops is not initialized, although the bbmap is.  weird.
  for (auto itr = function->begin(), end = function->end(); itr != end; ++itr) {
    BasicBlock *bb = itr;
    if (const Loop *loop = kloop.getLoopFor(bb)) {
      loops.insert(loop);
    }
  }
}

void KFunction::calcFnHash() {

  HashAccumulator hash;
  vector<const BasicBlock *> worklist;
  set<const BasicBlock *> visited;

  if (!function->empty()) {
    const BasicBlock *entry = &(function->getEntryBlock());
    worklist.push_back(entry);
    visited.insert(entry);
    while (!worklist.empty()) {
      const BasicBlock *bb = worklist.back();
      worklist.pop_back();

      // add a block header
      hash.add((uint64_t) 0x4df1d4db);
      uint64_t bb_value = calcBBHash(bb);
      bb_hashes[bb] = bb_value;
      hash.add(bb_value);

      const TerminatorInst *term = bb->getTerminator();
      for (unsigned idx = 0, end = term->getNumSuccessors(); idx != end; ++idx) {
        const BasicBlock *next = term->getSuccessor(idx);
        if (!(visited.insert(next).second)) continue;
        worklist.push_back(next);
      }
    }
  }
  while (hash.get() == 0) hash.add((uint64_t) 0xd4db4df1);  // no zero hash values
  fn_hash = hash.get();
}

uint64_t KFunction::getHashValue() {
  if (fn_hash == 0) calcFnHash();
  return fn_hash;
}

uint64_t KFunction::calcBBHash(const llvm::BasicBlock *bb) {

  HashAccumulator hash;
  for (auto &inst : *bb) {
    // add the instruction to the hash
    hash.add((uint64_t) inst.getOpcode());

    // call instruction to assert_fail needs special handling
    // one of the args contains a source line number that is expected
    // to change without effecting behavior
    if (const CallInst *ci = dyn_cast<CallInst>(&inst)) {
      if (Function *called = ci->getCalledFunction()) {
        string fn_name = ci->getName().str();
        if (assertionFns.contains(fn_name)) {
          hash.add(fn_name);
          continue;
        }
      }
    }

    if (const CmpInst *ci = dyn_cast<CmpInst>(&inst)) {
      hash.add((uint64_t) ci->getPredicate());
    }

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
  return hash.get();
}


KFunction::~KFunction() {
  for (unsigned i=0; i<numInstructions; ++i)
    delete instructions[i];
  delete[] instructions;
}

bool KFunction::reachesAnyOf(const llvm::BasicBlock *bb, const std::set_ex<const llvm::BasicBlock*> &blocks) const {

  // setup for BFS traversal of CFG
  std::set_ex<const llvm::BasicBlock*> visited;
  std::deque<const llvm::BasicBlock*> worklist;
  worklist.push_front(bb);

  while (!worklist.empty()) {

    const llvm::BasicBlock *current = worklist.front();
    worklist.pop_front();

    visited.insert(current);
    if (blocks.contains(current)) {
      return true;
    }

    BasicBlocks succs;
    getSuccessorBBs(current, succs);
    for (auto succ : succs) {
      if (!visited.contains(succ)) {
        worklist.push_back(succ);
      }
    }
  }
  return false;
}

void KFunction::getSuccessorBBs(const BasicBlock *bb, BasicBlocks &successors) const {

  successors.clear();
  for (auto itr = succ_begin(bb), end = succ_end(bb); itr != end; ++itr) {
    const BasicBlock *succ = *itr;
    if (succ != nullptr) {
      successors.insert(*itr);
    }
  }
}

void KFunction::getPredecessorBBs(const llvm::BasicBlock *bb, BasicBlocks &predecessors) const {

  predecessors.clear();
  for (auto itr = pred_begin(bb), end = pred_end(bb); itr != end; ++itr) {
    const BasicBlock *pred = *itr;
    if (pred != nullptr) {
      predecessors.insert(*itr);
    }
  }
}
