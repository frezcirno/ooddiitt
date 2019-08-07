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

#include "klee/Config/Version.h"
#include "klee/Interpreter.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ModuleUtil.h"

#include "llvm/Bitcode/ReaderWriter.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/TypeFinder.h"
#else
#include "llvm/Instructions.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/ValueSymbolTable.h"
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
#include "llvm/Target/TargetData.h"
#else
#include "llvm/DataLayout.h"
#endif

#endif

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#include "llvm/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/Path.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/ADT/PostOrderIterator.h"

#include <llvm/Transforms/Utils/Cloning.h>
#include <getopt.h>
#include <boost/algorithm/string.hpp>

using namespace llvm;
using namespace klee;
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

  cl::list<string>
  MergeAtExit("merge-at-exit");

  cl::opt<bool>
  OutputSource("output-source",
               cl::desc("Write the assembly for the final transformed source"),
               cl::init(false));

  cl::opt<bool>
  OutputModule("output-module",
               cl::desc("Write the bitcode for the final transformed module"),
               cl::init(false));

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

  cl::opt<bool>
  DebugPrintEscapingFunctions("debug-print-escaping-functions",
                              cl::desc("Print functions whose address is taken."));
}


// static data
const std::set<std::string> KModule::marker_fn_names = { "__MARK__", "__mark__", "__calltag__" };
const std::set<std::string> KModule::skip_fn_names = { "__init_markers__", "__term_markers__" };

KModule::KModule(Module *_module)
  : module(_module),
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
    targetData(new TargetData(module)),
#else
    targetData(new DataLayout(module)),
#endif
    kleeMergeFn(nullptr),
    infos(nullptr),
    constantTable(nullptr) {}

KModule::~KModule() {
  delete[] constantTable;
  delete infos;

  for (auto it = functions.begin(), ie = functions.end(); it != ie; ++it)
    delete *it;

  for (auto it=constantMap.begin(), itE=constantMap.end(); it!=itE;++it)
    delete it->second;

  delete targetData;
  delete module;
}

/***/

namespace llvm {
extern void Optimize(Module *, const string &EntryPoint);
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

bool KModule::addInternalFunction(string name) {

  Function *fn = module->getFunction(name);
  if (fn != nullptr) {
    addInternalFunction(fn);
    return true;
  }
  return false;
}

void KModule::prepare(const Interpreter::ModuleOptions &opts, InterpreterHandler *ih) {

  LLVMContext &ctx = module->getContext();

  // gather a list of original module functions
  set<const Function*> orig_functions;
  for (auto itr = module->begin(), end = module->end(); itr != end; ++itr) {
    Function *fn = itr;
    if (!fn->isDeclaration()) {
      orig_functions.insert(fn);
    }
  }

  // find each marker function and add to set
  for (const auto &name : marker_fn_names) {
    if (const Function *fn = module->getFunction(name)) {
      marker_fns.insert(fn);
    }
  }

  for (const auto &name : skip_fn_names) {
    if (const Function *fn = module->getFunction(name)) {
      skip_fns.insert(fn);
    }
  }

  if (!MergeAtExit.empty()) {
    Function *mergeFn = module->getFunction("klee_merge");
    if (!mergeFn) {
      LLVM_TYPE_Q llvm::FunctionType *Ty =
        FunctionType::get(Type::getVoidTy(ctx),
                          vector<LLVM_TYPE_Q Type*>(), false);
      mergeFn = Function::Create(Ty, GlobalVariable::ExternalLinkage,
				 "klee_merge",
				 module);
    }

    for (auto it = MergeAtExit.begin(), ie = MergeAtExit.end(); it != ie; ++it) {
      string &name = *it;
      Function *f = module->getFunction(name);
      if (!f) {
        klee_error("cannot insert merge-at-exit for: %s (cannot find)", name.c_str());
      } else if (f->isDeclaration()) {
        klee_error("cannot insert merge-at-exit for: %s (external)", name.c_str());
      }

      BasicBlock *exit = BasicBlock::Create(ctx, "exit", f);
      PHINode *result = 0;
      if (f->getReturnType() != Type::getVoidTy(ctx))
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 0)
        result = PHINode::Create(f->getReturnType(), 0, "retval", exit);
#else
		result = PHINode::Create(f->getReturnType(), "retval", exit);
#endif
      CallInst::Create(mergeFn, "", exit);
      ReturnInst::Create(ctx, result, exit);

      llvm::errs() << "KLEE: adding klee_merge at exit of: " << name << "\n";
      for (llvm::Function::iterator bbit = f->begin(), bbie = f->end(); bbit != bbie; ++bbit) {
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
    Interpreter *i = ih->getInterpreter();

    // don't use the overshift pass in zop mode, incorrectly terminates paths
    if (opts.CheckOvershift && i != nullptr &&  i->getOptions().mode != Interpreter::zop) {
      pm.add(new OvershiftCheckPass());
    }
    // FIXME: This false here is to work around a bug in
    // IntrinsicLowering which caches values which may eventually be
    // deleted (via RAUW). This can be removed once LLVM fixes this
    // issue.
    pm.add(new IntrinsicCleanerPass(*targetData, false));
    pm.run(*module);
  }

  if (opts.Optimize)
    Optimize(module, opts.EntryPoint);
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 3)
  // Force importing functions required by intrinsic lowering. Kind of
  // unfortunate clutter when we don't need them but we won't know
  // that until after all linking and intrinsic lowering is
  // done. After linking and passes we just try to manually trim these
  // by name. We only add them if such a function doesn't exist to
  // avoid creating stale uses.

  LLVM_TYPE_Q llvm::Type *i8Ty = Type::getInt8Ty(ctx);
  forceImport(module, "memcpy", PointerType::getUnqual(i8Ty),
              PointerType::getUnqual(i8Ty),
              PointerType::getUnqual(i8Ty),
              targetData->getIntPtrType(ctx), (Type*) 0);
  forceImport(module, "memmove", PointerType::getUnqual(i8Ty),
              PointerType::getUnqual(i8Ty),
              PointerType::getUnqual(i8Ty),
              targetData->getIntPtrType(ctx), (Type*) 0);
  forceImport(module, "memset", PointerType::getUnqual(i8Ty),
              PointerType::getUnqual(i8Ty),
              Type::getInt32Ty(ctx),
              targetData->getIntPtrType(ctx), (Type*) 0);
#endif
  // FIXME: Missing force import for various math functions.

  // FIXME: Find a way that we can test programs without requiring
  // this to be linked in, it makes low level debugging much more
  // annoying.


  SmallString<128> LibPath(opts.LibraryDir);
  string intrinsicLib = "kleeRuntimeIntrinsic";
  Expr::Width width = targetData->getPointerSizeInBits();

  if (width == Expr::Int32) {
    intrinsicLib += "-32";
  } else if (width == Expr::Int64) {
    intrinsicLib += "-64";
  }

  intrinsicLib += ".bc";
  llvm::sys::path::append(LibPath,intrinsicLib);
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
    pm.add(new IntrinsicCleanerPass(*targetData));
    pm.add(new PhiCleanerPass());
    pm.add(new SplitInitPass(this));
    pm.run(*module);
  }

  infos = new InstructionInfoTable(module);

  // Write out the .ll assembly file. We truncate long lines to work
  // around a kcachegrind parsing bug (it puts them on new lines), so
  // that source browsing works.
  if (OutputSource || opts.OutputSource) {
    llvm::raw_fd_ostream *os = ih->openOutputFile("assembly.ll", true);
    if (os != nullptr) {
        *os << *module;
        delete os;
    }
  }

  // RLR TODO: move to llvm static analysis pass
# if 0 == 1
  if (OutputStatic) {
    llvm::raw_fd_ostream *os = ih->openOutputFile("structs.json", true);
    if (os != nullptr) {

      llvm::TypeFinder typeFinder;
      typeFinder.run(*module, false);

      *os << "{";
      unsigned struct_cnt = 0;
      for (auto type : typeFinder) {

        if (StructType *st = dyn_cast<StructType>(type)) {

          if (st->hasName()) {
            string name = st->getName();
            if (struct_cnt++ > 0)
              *os << ",";

            *os << "\n  \"" << name << "\": {\n    \"size\": ";

            const StructLayout *targetStruct = targetData->getStructLayout(st);
            uint64_t size = targetStruct->getSizeInBytes();

            *os << size << ",\n    \"types\": [";
            for (unsigned idx=0, end=st->getNumElements(); idx < end; ++idx) {
              if (idx > 0) *os << ", ";
              *os << "\"" << ih->getTypeName(st->getElementType(idx)) << "\"";
            }
            *os << "],\n";

            *os << "    \"offsets\": [";
            for (unsigned idx=0, end=st->getNumElements(); idx < end; ++idx) {
              if (idx > 0) *os << ", ";
              *os << targetStruct->getElementOffset(idx);
            }
            *os << "],\n";

            *os << "    \"sizes\": [";
            for (unsigned idx=0, end=st->getNumElements(); idx < end; ++idx) {
              if (idx > 0) *os << ", ";
              *os << targetData->getTypeSizeInBits(st->getElementType(idx)) / 8;
            }
            *os << "]\n  }";
          }
        }
      }

      *os << "\n}\n";
      delete os;
    }
  }
#endif

  if (OutputModule) {
    llvm::raw_fd_ostream *os = ih->openOutputFile("assembly.bc");
    if (os != nullptr) {
      WriteBitcodeToFile(module, *os);
      delete os;
    }
  }

  kleeMergeFn = module->getFunction("klee_merge");

  /* Build shadow structures */
  infos = new InstructionInfoTable(module);

  // never stub some functions
  addInternalFunction("__ctype_b_loc");

  for (auto it = module->begin(), ie = module->end(); it != ie; ++it) {
    if (it->isDeclaration())
      continue;

    Function *fn = static_cast<Function *>(it);

    // if we just added this function, then its either klee runtime or an intrinsic
    if (orig_functions.count(fn) == 0) {
      addInternalFunction(fn);
    }

    KFunction *kf = new KFunction(fn, this);

    for (unsigned i=0; i<kf->numInstructions; ++i) {
      KInstruction *ki = kf->instructions[i];
      ki->info = &infos->getInfo(ki->inst);
    }

    functions.push_back(kf);
    functionMap.insert(make_pair(fn, kf));
  }

  /* Compute various interesting properties */

  // check for annotation functions
  // construct a list of data types, by name, for annotation matching
  map<string,Type*> mapNameToType;
  llvm::TypeFinder typeFinder;
  typeFinder.run(*module, true);
  for (auto type : typeFinder) {
    std::string name = type->getName().str();
    if (boost::starts_with(name, "struct.")) {
      name = name.substr(7);
    }
    mapNameToType[name] = type;
  }

  for (auto it = functions.begin(), ie = functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    const Function *fn = kf->function;
    std::string full_name = fn->getName();
    if (fn->getReturnType()->isVoidTy() && boost::starts_with(full_name, "annot_")) {
      std::string target_name = full_name.substr(6);
      if (!target_name.empty()) {
        if (Function *target = module->getFunction(target_name)) {

          // this is a function annotation
          if (!MatchSignature(target, fn)) {
            klee_error("Function annotation for %s has mismtached argument types", full_name.c_str());
          }
          functionMap[target]->annotationKFn = kf;
        } else {

          auto itr = mapNameToType.find(target_name);
          if (itr != mapNameToType.end()) {

            // this is a type annotation
            Type *tptr = PointerType::get(itr->second, 0);
            if (!MatchSignature(tptr, fn)) {
              klee_error("Type annotation for %s has incorrect argument type", full_name.c_str());
            }
            mapTypeToAnnotation[tptr] = kf;

          } else {

            // annotation cannot be associated with either function or data type
            // report error
            klee_error("Cannot find annotation association for %s", full_name.c_str());
          }
        }
      }
    }
  }

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

bool KModule::MatchSignature(const Function *fn, const Function *annotFn) const {

  if (annotFn->getReturnType()->isVoidTy()) {
    if (fn->arg_size() == annotFn->arg_size()) {

      // collect all of the argument types
      vector<const Type*> fnArgTypes;
      vector<const Type*> annotArgTypes;
      for (auto ai = fn->arg_begin(), ae = fn->arg_end(); ai != ae; ++ai) {
        fnArgTypes.push_back(ai->getType());
      }
      for (auto ai = annotFn->arg_begin(), ae = annotFn->arg_end(); ai != ae; ++ai) {
        annotArgTypes.push_back(ai->getType());
      }

      // number of args is the same so size of arrays should be the same as well
      assert(fnArgTypes.size() == annotArgTypes.size());

      // if any argument has a different type, then this is not a match
      for (unsigned index = 0, end = (unsigned) fnArgTypes.size(); index < end; ++index) {
        if (fnArgTypes[index] != annotArgTypes[index]) {
          return false;
        }
      }

      // all argument types match
      return true;
    }
  }
  return false;
}

bool KModule::MatchSignature(const Type *type, const Function *annotFn) const {

  if (annotFn->getReturnType()->isVoidTy()) {

    unsigned index = 0;
    for (auto ai = annotFn->arg_begin(), ae = annotFn->arg_end(); ai != ae; ++ai, ++index) {

      const Argument &arg = *ai;
      if (type != arg.getType()) {
        return false;
      }
    }
    return index == 1;
  }
  return false;
}

void KModule::prepareMarkers(const Interpreter::ModuleOptions &opts, InterpreterHandler *ih, const ProgInfo &info) {

  // RLR TODO: move to llvm static analysis pass
#if 0  == 1
  set<const Function *> fns_ptr_relation;
  set<const Function *> fns_ptr_equality;
  set<const Function *> fns_ptr_equal_non_null_const;
  set<const Function *> fns_ptr_to_int;
  set<const Function *> fns_int_to_ptr;
#endif

  // for each function in the main module
  for (auto it = functions.begin(), ie = functions.end(); it != ie; ++it) {

    KFunction *kf = *it;
    Function *fn = kf->function;
    string fn_name = fn->getName().str();
    kf->fnID = info.getFnID(fn_name);

    if (kf->fnID != 0) {

      set<unsigned> fn_bbs;

      // now step through each of the functions basic blocks
      for (auto bbit = fn->begin(), bbie = fn->end(); bbit != bbie; ++bbit) {
        const BasicBlock &bb = *bbit;

        // look through each instruction of the bb looking for function calls
        // and problematic instructions
        vector<unsigned> bbIDs;
        for (auto iit = bb.begin(), iid = bb.end(); iit != iid; ++iit) {
          const Instruction *i = &(*iit);
          unsigned opcode = i->getOpcode();
          if (opcode == Instruction::Call) {

            const CallSite cs(const_cast<Instruction *>(i));

            Function *called = getTargetFunction(cs.getCalledValue());
            if (called != nullptr) {

              // check the name, number of arguments, and the return type
              if (isMarkerFn(called) && (called->arg_size() == 2) && (called->getReturnType()->isVoidTy())) {

                // extract the two literal arguments
                const Constant *arg0 = dyn_cast<Constant>(cs.getArgument(0));
                const Constant *arg1 = dyn_cast<Constant>(cs.getArgument(1));
                if ((arg0 != nullptr) && (arg1 != nullptr)) {
                  unsigned val0 = (unsigned) arg0->getUniqueInteger().getZExtValue();
                  unsigned val1 = (unsigned) arg1->getUniqueInteger().getZExtValue();

                  if (val0 != kf->fnID) {
                    klee_warning("conflicting marker function id, received %d, expected %d", val0, kf->fnID);
                  }
                  bbIDs.push_back(val1);
                  kf->mapBBlocks[val1] = &bb;
                }
              }
            }
// RLR TODO: move to llvm static analysis
#if 0 == 1
          } else if (opcode == Instruction::ICmp) {

            const CmpInst *ci = cast<CmpInst>(i);
            const Value *arg0 = ci->getOperand(0);
            const Value *arg1 = ci->getOperand(1);

            if (arg0->getType()->isPointerTy()) {
              if (ci->isEquality()) {
                const Constant *carg0 = dyn_cast<Constant>(arg0);
                const Constant *carg1 = dyn_cast<Constant>(arg1);
                if ((carg0 == nullptr) && (carg1 == nullptr)) {
                  fns_ptr_equality.insert(fn);
                } else {
                  if (((carg0 != nullptr) && !carg0->isNullValue()) ||
                      ((carg1 != nullptr) && !carg1->isNullValue())) {
                    fns_ptr_equal_non_null_const.insert(fn);
                  }
                }
              } else {
                fns_ptr_relation.insert(fn);
              }
            }
          } else if (opcode == Instruction::PtrToInt) {
            fns_ptr_to_int.insert(fn);
          } else if (opcode == Instruction::IntToPtr) {
            fns_int_to_ptr.insert(fn);
#endif
          }
        }
        kf->mapMarkers[&bb] = bbIDs;
      }

      // generate loop information for this fn
      kf->domTree.runOnFunction(*fn);
      auto &base = kf->loopInfo.getBase();
      base.Analyze(kf->domTree.getBase());
    }
  }

// RLR TODO: move to llvm static analysis pass
#if 0 == 1
  if (OutputStatic) {

    // save a json formatted record of found pointer relations
    llvm::raw_fd_ostream *os = ih->openOutputFile("ptr_relations.json", true);
    if (os != nullptr) {

      unsigned counter = 0;

      *os << "{\n";

      EmitFunctionSet(os, "ptr_equality", fns_ptr_equality, counter);
      EmitFunctionSet(os, "ptr_relation", fns_ptr_relation, counter);
      EmitFunctionSet(os, "ptr_equal_non_null", fns_ptr_equal_non_null_const, counter);
      EmitFunctionSet(os, "ptr_to_int", fns_ptr_to_int, counter);
      EmitFunctionSet(os, "ptr_int_to_ptr", fns_int_to_ptr, counter);

      if (counter > 0) {
        *os << "\n";
      }
      *os << "}\n";
      delete os;
    }
  }
#endif
}

// RLR TODO: move to llvm static analysis pass
#if 0 == 1
void KModule::EmitFunctionSet(raw_fd_ostream *os,
                              string key,
                              set<const Function*> fns,
                              unsigned &counter_keys) {

  if (!fns.empty()) {
    if (counter_keys > 0) {
      *os << ",\n";
    }
    counter_keys += 1;

    unsigned counter_elements = 0;
    *os << "  \"" << key << "\": [\n";
    for (auto fn : fns) {
      if (counter_elements > 0) {
        *os << ",\n";
      }
      *os << "    \"" << fn->getName().str() << "\"";
      counter_elements += 1;
    }
    *os << "\n  ]";
  }
}
#endif

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

KFunction::KFunction(llvm::Function *_function,
                     KModule *km)
  : function(_function),
    numArgs((unsigned) function->arg_size()),
    numInstructions(0),
    trackCoverage(true),
    fnID(0),
    annotationKFn(nullptr) {

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
}

KFunction::~KFunction() {
  for (unsigned i=0; i<numInstructions; ++i)
    delete instructions[i];
  delete[] instructions;
}

bool KFunction::reachesAnyOf(const llvm::BasicBlock *bb, const std::set<const llvm::BasicBlock*> &blocks) const {

  // setup for BFS traversal of CFG
  std::set<const llvm::BasicBlock*> visited;
  std::deque<const llvm::BasicBlock*> worklist;
  worklist.push_front(bb);

  while (!worklist.empty()) {

    const llvm::BasicBlock *current = worklist.front();
    worklist.pop_front();

    visited.insert(current);
    if (blocks.count(current) > 0) {
      return true;
    }

    BasicBlocks succs;
    getSuccessorBBs(current, succs);
    for (auto succ : succs) {
      if (visited.count(succ) == 0) {
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

void KFunction::constructSortedBBlocks(deque<unsigned> &sortedList, const BasicBlock *entry) {

  sortedList.clear();
  if (entry == nullptr) {
    entry = &function->getEntryBlock();
  }

  ReversePostOrderTraversal<const BasicBlock*> RPO(entry);
  for (const auto &bb : RPO) {
    const auto &itr = mapMarkers.find(bb);
    if (itr != mapMarkers.end() && !itr->second.empty()) {
      sortedList.push_back(itr->second.front());
    }
  }
}
