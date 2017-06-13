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
#include "llvm/Analysis/Dominators.h"
#include "llvm/IR/Instruction.h"

#include <llvm/Transforms/Utils/Cloning.h>

using namespace llvm;
using namespace klee;

namespace {
  enum SwitchImplType {
    eSwitchTypeSimple,
    eSwitchTypeLLVM,
    eSwitchTypeInternal
  };

  cl::list<std::string>
  MergeAtExit("merge-at-exit");
    
  cl::opt<bool>
  NoTruncateSourceLines("no-truncate-source-lines",
                        cl::desc("Don't truncate long lines in the output source"));

  cl::opt<bool>
  OutputSource("output-source",
               cl::desc("Write the assembly for the final transformed source"),
               cl::init(true));

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

KModule::KModule(Module *_module) 
  : module(_module),
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
    targetData(new TargetData(module)),
#else
    targetData(new DataLayout(module)),
#endif
    kleeMergeFn(0),
    infos(0),
    constantTable(0) {
}

KModule::~KModule() {
  delete[] constantTable;
  delete infos;

  for (std::vector<KFunction*>::iterator it = functions.begin(), 
         ie = functions.end(); it != ie; ++it)
    delete *it;

  for (std::map<llvm::Constant*, KConstant*>::iterator it=constantMap.begin(),
      itE=constantMap.end(); it!=itE;++it)
    delete it->second;

  delete targetData;
  delete module;
}

/***/

namespace llvm {
extern void Optimize(Module *, const std::string &EntryPoint);
}

// what a hack
static Function *getStubFunctionForCtorList(Module *m,
                                            GlobalVariable *gv, 
                                            std::string name) {
  assert(!gv->isDeclaration() && !gv->hasInternalLinkage() &&
         "do not support old LLVM style constructor/destructor lists");
  
  std::vector<LLVM_TYPE_Q Type*> nullary;

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

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 3)
static void forceImport(Module *m, const char *name, LLVM_TYPE_Q Type *retType,
                        ...) {
  // If module lacks an externally visible symbol for the name then we
  // need to create one. We have to look in the symbol table because
  // we want to check everything (global variables, functions, and
  // aliases).

  Value *v = m->getValueSymbolTable().lookup(name);
  GlobalValue *gv = dyn_cast_or_null<GlobalValue>(v);

  if (!gv || gv->hasInternalLinkage()) {
    va_list ap;

    va_start(ap, retType);
    std::vector<LLVM_TYPE_Q Type *> argTypes;
    while (LLVM_TYPE_Q Type *t = va_arg(ap, LLVM_TYPE_Q Type*))
      argTypes.push_back(t);
    va_end(ap);

    m->getOrInsertFunction(name, FunctionType::get(retType, argTypes, false));
  }
}
#endif


void KModule::addInternalFunction(std::string functionName){
  Function* internalFunction = module->getFunction(functionName);
  if (!internalFunction) {
    KLEE_DEBUG(klee_warning(
        "Failed to add internal function %s. Not found.", functionName));
    return ;
  }
  KLEE_DEBUG(klee_message("Added function %s.",functionName));
  internalFunctions.insert(internalFunction);
  concreteFunctions.insert(internalFunction);
}

void KModule::addConcreteFunction(std::string fnName) {

  const llvm::Function *fn = module->getFunction(fnName);
  if (fn != nullptr) addConcreteFunction(fn);
}


void KModule::prepare(const Interpreter::ModuleOptions &opts,
                      InterpreterHandler *ih) {

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
  PassManager pm;
  pm.add(new RaiseAsmPass());
  if (opts.CheckDivZero) pm.add(new DivCheckPass());
  if (opts.CheckOvershift) pm.add(new OvershiftCheckPass());
  // FIXME: This false here is to work around a bug in
  // IntrinsicLowering which caches values which may eventually be
  // deleted (via RAUW). This can be removed once LLVM fixes this
  // issue.
  pm.add(new IntrinsicCleanerPass(*targetData, false));
  pm.run(*module);

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
  llvm::sys::path::append(LibPath,
#if LLVM_VERSION_CODE >= LLVM_VERSION(3,3)
      "kleeRuntimeIntrinsic.bc"
#else
      "libkleeRuntimeIntrinsic.bca"
#endif
    );
  module = linkWithLibrary(module, LibPath.str());

  // Add internal functions which are not used to check if instructions
  // have been already visited
  if (opts.CheckDivZero)
    addInternalFunction("klee_div_zero_check");
  if (opts.CheckOvershift)
    addInternalFunction("klee_overshift_check");


  // Needs to happen after linking (since ctors/dtors can be modified)
  // and optimization (since global optimization can rewrite lists).
  injectStaticConstructorsAndDestructors(module);

  // Finally, run the passes that maintain invariants we expect during
  // interpretation. We run the intrinsic cleaner just in case we
  // linked in something with intrinsics but any external calls are
  // going to be unresolved. We really need to handle the intrinsics
  // directly I think?
  PassManager pm3;
  pm3.add(createCFGSimplificationPass());
  switch(SwitchType) {
  case eSwitchTypeInternal: break;
  case eSwitchTypeSimple: pm3.add(new LowerSwitchPass()); break;
  case eSwitchTypeLLVM:  pm3.add(createLowerSwitchPass()); break;
  default: klee_error("invalid --switch-type");
  }
  pm3.add(new IntrinsicCleanerPass(*targetData));
  pm3.add(new PhiCleanerPass());
  pm3.run(*module);
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 3)
  // For cleanliness see if we can discard any of the functions we
  // forced to import.
  Function *f;
  f = module->getFunction("memcpy");
  if (f && f->use_empty()) f->eraseFromParent();
  f = module->getFunction("memmove");
  if (f && f->use_empty()) f->eraseFromParent();
  f = module->getFunction("memset");
  if (f && f->use_empty()) f->eraseFromParent();
#endif

  // Write out the .ll assembly file. We truncate long lines to work
  // around a kcachegrind parsing bug (it puts them on new lines), so
  // that source browsing works.
  if (OutputSource) {
    llvm::raw_fd_ostream *os = ih->openOutputFile("assembly.ll");
    assert(os && !os->has_error() && "unable to open source output");

    // We have an option for this in case the user wants a .ll they
    // can compile.
    if (NoTruncateSourceLines) {
      *os << *module;
    } else {
      std::string string;
      llvm::raw_string_ostream rss(string);
      rss << *module;
      rss.flush();
      const char *position = string.c_str();

      for (;;) {
        const char *end = index(position, '\n');
        if (!end) {
          *os << position;
          break;
        } else {
          unsigned count = (end - position) + 1;
          if (count<255) {
            os->write(position, count);
          } else {
            os->write(position, 254);
            *os << "\n";
          }
          position = end+1;
        }
      }
    }
    delete os;
  }

  if (OutputModule) {
    llvm::raw_fd_ostream *f = ih->openOutputFile("final.bc");
    WriteBitcodeToFile(module, *f);
    delete f;
  }

  kleeMergeFn = module->getFunction("klee_merge");

  /* Build shadow structures */

  infos = new InstructionInfoTable(module);  
  
  for (Module::iterator it = module->begin(), ie = module->end();
       it != ie; ++it) {
    if (it->isDeclaration())
      continue;

    Function *fn = static_cast<Function *>(it);
    KFunction *kf = new KFunction(fn, this);
    
    for (unsigned i=0; i<kf->numInstructions; ++i) {
      KInstruction *ki = kf->instructions[i];
      ki->info = &infos->getInfo(ki->inst);
    }

    functions.push_back(kf);
    functionMap.insert(std::make_pair(fn, kf));
  }

  /* Compute various interesting properties */

  for (std::vector<KFunction*>::iterator it = functions.begin(), 
         ie = functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    if (functionEscapes(kf->function))
      escapingFunctions.insert(kf->function);
  }

  if (DebugPrintEscapingFunctions && !escapingFunctions.empty()) {
    llvm::errs() << "KLEE: escaping functions: [";
    for (std::set<Function*>::iterator it = escapingFunctions.begin(), 
         ie = escapingFunctions.end(); it != ie; ++it) {
      llvm::errs() << (*it)->getName() << ", ";
    }
    llvm::errs() << "]\n";
  }
}


void KModule::prepareMarkers() {

  // for each function in the main module
  for (auto it = functions.begin(), ie = functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    const Function *fn = kf->function;
    std::string fnName = fn->getName();
    unsigned fnID = 0;

    // now step through each of the functions basic blocks
    for (auto bbit = fn->begin(), bbie = fn->end(); bbit != bbie; ++bbit) {
      const BasicBlock &bb = *bbit;

      // look through each instruction of the bb looking for function calls
      // use reverse iterator so we find the first bbid last (single bb function will have two)
      bool isMajor = false;
      std::vector<unsigned> bbIDs;
      for (auto iit = bb.begin(), iid = bb.end(); iit != iid; ++iit) {
        const Instruction *i = &(*iit);
        if (i->getOpcode() == Instruction::Call) {

          // RLR TODO: eval this for callsite instead of CallInst
          const CallInst *ci = cast<CallInst>(i);

          // check if this is a call to either marker
          Function *called = ci->getCalledFunction();
          if (called == nullptr) {
            klee_warning("mystery CallInst failure at setup");
          } else {

            std::string calledName = called->getName();

            // check the name, number of arguments, and the return type
            if (((calledName == "MARK") || (calledName == "mark")) &&
                (called->arg_size() == 2) &&
                (called->getReturnType()->isVoidTy())) {

              // extract the two literal arguments
              const Constant *arg0 = dyn_cast<Constant>(ci->getArgOperand(0));
              const Constant *arg1 = dyn_cast<Constant>(ci->getArgOperand(1));
              if ((arg0 != nullptr) && (arg1 != nullptr)) {
                fnID = (unsigned) arg0->getUniqueInteger().getZExtValue();
                unsigned bbID = (unsigned) arg1->getUniqueInteger().getZExtValue();
                bbIDs.push_back(bbID);

                if (calledName == "MARK") {
                  isMajor = true;
                }
              }
            } else if (!isConcreteFunction(called)) {
              isMajor = true;
            }
          }
        }
      }
      if (bbIDs.size() > 0) {
        kf->mapMarkers[&bb] = bbIDs;
        if (isMajor) {
          kf->majorMarkers.insert((fnID * 1000) + bbIDs.front());
        }
      }
    }
    kf->fnID = fnID;

    // if this function is marked, enumerate all of the m2m_paths
    if (kf->fnID != 0) {

      // find all (possibly nested) loop headers
      kf->findLoopHeaders();

      // and find all simple paths for cycles
      // beginning with each loop header
      bb_paths_t paths;
      for (const auto pr : kf->loopInfo) {
        kf->addAllSimpleCycles(pr.first, paths);
      }

      // create a list of bbs that belong to each cycle found above
      for (const auto path : paths) {

        const BasicBlock *hdr = path.front();

        assert(kf->isLoopHeader(hdr));

        KLoopInfo &info = kf->loopInfo[hdr];
        for (const BasicBlock *bb : path) {
          info.bbs.insert(bb);
        }
      }

      // iterate over each loop and each basic block to
      // find the exit nodes
      for (auto pr : kf->loopInfo) {

        const BasicBlock *hdr = pr.first;
        KLoopInfo &info = kf->loopInfo[hdr];

        for (const BasicBlock *bb : info.bbs) {
          BasicBlocks successors;
          kf->getSuccessorBBs(bb, successors);

          // if any successor is not in loop, then
          // it is an exit node
          for (const auto succ : successors) {
            if (!kf->isInLoop(hdr, succ)) {
              info.exits.insert(bb);
              break;
            }
          }
        }
      }

      // find all simple paths from entry to exit
      kf->addAllSimplePaths(paths);

      kf->setM2MPaths(paths);
    }
  }
}

KConstant* KModule::getKConstant(Constant *c) {
  std::map<llvm::Constant*, KConstant*>::iterator it = constantMap.find(c);
  if (it != constantMap.end())
    return it->second;
  return NULL;
}

unsigned KModule::getConstantID(Constant *c, KInstruction* ki) {
  KConstant *kc = getKConstant(c);
  if (kc)
    return kc->id;  

  unsigned id = constants.size();
  kc = new KConstant(c, id, ki);
  constantMap.insert(std::make_pair(c, kc));
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
                         std::map<Instruction*, unsigned> &registerMap,
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
    numArgs(function->arg_size()),
    numInstructions(0),
    trackCoverage(true),
    fnID(0) {

  for (llvm::Function::iterator bbit = function->begin(),
         bbie = function->end(); bbit != bbie; ++bbit) {
    BasicBlock *bb = static_cast<BasicBlock *>(bbit);
    basicBlockEntry[bb] = numInstructions;
    numInstructions += bb->size();
  }

  instructions = new KInstruction*[numInstructions];

  std::map<Instruction*, unsigned> registerMap;

  // The first arg_size() registers are reserved for formals.
  unsigned rnum = numArgs;
  for (llvm::Function::iterator bbit = function->begin(), 
         bbie = function->end(); bbit != bbie; ++bbit) {
    for (llvm::BasicBlock::iterator it = bbit->begin(), ie = bbit->end();
         it != ie; ++it)
      registerMap[static_cast<Instruction *>(it)] = rnum++;
  }
  numRegisters = rnum;
  
  unsigned i = 0;
  for (llvm::Function::iterator bbit = function->begin(), 
         bbie = function->end(); bbit != bbie; ++bbit) {
    for (llvm::BasicBlock::iterator it = bbit->begin(), ie = bbit->end();
         it != ie; ++it) {
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

// RLR TODO: this could use some commentary...
void KFunction::addAllSimplePaths(bb_paths_t &paths) const {

  std::set<const BasicBlock*> visited;
  bb_path_t path;

  recurseAllSimplePaths(&function->getEntryBlock(), visited, path, paths);
}

void KFunction::recurseAllSimplePaths(const BasicBlock *bb,
                                      std::set<const BasicBlock*> &visited,
                                      bb_path_t &path,
                                      bb_paths_t &paths) const {
  visited.insert(bb);
  path.push_back(bb);

  BasicBlocks successors;
  getSuccessorBBs(bb, successors);

  // if bb has no successors, then we have a path
  if (successors.empty()) {
    paths.insert(path);
  } else {
    for (auto itr = successors.begin(), end = successors.end(); itr != end; ++itr) {
      const BasicBlock *succ = *itr;
      if (visited.find(succ) == visited.end()) {
        recurseAllSimplePaths(succ, visited, path, paths);
      }
    }
  }

  path.pop_back();
  visited.erase(bb);
}

void KFunction::addAllSimpleCycles(const BasicBlock *bb, bb_paths_t &paths) const {

  std::set<const BasicBlock*> visited;
  bb_path_t path;

  recurseAllSimpleCycles(bb, bb, visited, path, paths);
}

void KFunction::recurseAllSimpleCycles(const BasicBlock *bb,
                                       const BasicBlock *dst,
                                       std::set<const BasicBlock*> &visited,
                                       bb_path_t &path,
                                       bb_paths_t &paths) const {

  visited.insert(bb);
  path.push_back(bb);

  BasicBlocks successors;
  getSuccessorBBs(bb, successors);
  for (auto itr = successors.begin(), end = successors.end(); itr != end; ++itr) {
    const BasicBlock *succ = *itr;

    if (succ == dst) {
      path.push_back(dst);
      paths.insert(path);
    } else if (visited.find(succ) == visited.end()) {
      recurseAllSimpleCycles(succ, dst, visited, path, paths);
    }
  }

  path.pop_back();
  visited.erase(bb);
}


void KFunction::translateBBPath2MarkerPath(const bb_path_t &bb_path, marker_path_t &marker_path) const {

  for (auto itr = bb_path.begin(), end = bb_path.end(); itr != end; ++itr) {

    const auto &markers = mapMarkers.find(*itr);

    // skip unmarked basic blocks
    if (markers != mapMarkers.end()) {
      for (unsigned bbID : markers->second) {
        marker_path.push_back((fnID * 1000) + bbID);
      }
    }
  }
}

void KFunction::setM2MPaths(const bb_paths_t &bb_paths) {


  m2m_paths.clear();

  // for each bb path, translate to marker path
  for (auto itr1 = bb_paths.begin(), end1 = bb_paths.end(); itr1 != end1; ++itr1) {

    const bb_path_t &bb_path = *itr1;
    marker_path_t marker_path;

    translateBBPath2MarkerPath(bb_path, marker_path);
    assert(marker_path.size() > 0 && isMajorMarker(marker_path.front()) && "Invalid marker path");

    marker_path_t m2m_path;
    for (auto itr2 = marker_path.begin(), end2 = marker_path.end(); itr2 != end2; ++itr2) {

      unsigned marker = *itr2;
      m2m_path.push_back(marker);
      if (isMajorMarker(marker) && (itr2 != marker_path.begin())) {
        m2m_paths.insert(m2m_path);
        m2m_path.clear();
        m2m_path.push_back(marker);
      }
    }
    if (m2m_path.size() > 0 && !isMajorMarker(m2m_path.back())) {
      m2m_paths.insert(m2m_path);
    }
  }
}

void KFunction::findLoopHeaders() {

  DominatorTree domTree;
  domTree.runOnFunction(*function);

  for (const BasicBlock &bb : *function) {

    BasicBlocks successors;
    getSuccessorBBs(&bb, successors);
    for (const BasicBlock *succ : successors) {
      if (domTree.dominates(succ, &bb)) {
        KLoopInfo &info = loopInfo[succ];
        (void) info;
      }
    }
  }
}

void KFunction::getSuccessorBBs(const BasicBlock *bb, BasicBlocks &successors) const {

  successors.clear();
  const TerminatorInst *tinst = bb->getTerminator();
  for (unsigned index = 0, num_succ = tinst->getNumSuccessors(); index < num_succ; ++index) {
    successors.insert(tinst->getSuccessor(index));
  }
}


bool KFunction::isInLoop(const llvm::BasicBlock *hdr, const llvm::BasicBlock *bb) const {

  assert(isLoopHeader(hdr));

  const auto &pr = loopInfo.find(hdr);
  if (pr != loopInfo.end()) {
    const KLoopInfo &info = pr->second;
    return info.bbs.find(bb) != info.bbs.end();
  }
  return false;
}

bool KFunction::isLoopExit(const llvm::BasicBlock *hdr, const llvm::BasicBlock *bb) const {

  assert(isLoopHeader(hdr));

  const auto &pr = loopInfo.find(hdr);
  if (pr != loopInfo.end()) {
    const KLoopInfo &info = pr->second;
    return info.exits.find(bb) != info.exits.end();
  }
  return false;
}
