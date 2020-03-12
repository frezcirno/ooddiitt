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
#include "klee/Internal/System/Memory.h"

#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/DataLayout.h"
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
#include <llvm/Analysis/LoopPass.h>

#include "klee/Internal/Module/ModuleTypes.h"

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
    module_trace(TraceType::invalid)
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

void KModule::transform(const Interpreter::ModuleOptions &opts,
                        const set<Function*> &module_fns,
                        const set<GlobalVariable*> &module_gbs,
                        TraceType ttrace,
                        MarkScope mscope) {

  assert(module != nullptr);

  set<Function*> fns_to_mark;
  if (mscope == MarkScope::module) {
    fns_to_mark = module_fns;
  } else if (mscope == MarkScope::all) {
    for (auto itr = module->begin(), end = module->end(); itr != end; ++itr) {
      fns_to_mark.insert(itr);
    }
  }

  LLVMContext &ctx = module->getContext();

  if (!MergeAtExit.empty()) {
    Function *mergeFn = module->getFunction("klee_merge");
    if (!mergeFn) {
      LLVM_TYPE_Q llvm::FunctionType *Ty = FunctionType::get(Type::getVoidTy(ctx), vector<LLVM_TYPE_Q Type *>(), false);
      mergeFn = Function::Create(Ty, GlobalVariable::ExternalLinkage, "klee_merge", module);
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
        result = PHINode::Create(f->getReturnType(), 0, "retval", exit);
      CallInst::Create(mergeFn, "", exit);
      ReturnInst::Create(ctx, result, exit);

      llvm::errs() << "KLEE: adding klee_merge at exit of: " << name << "\n";
      for (llvm::Function::iterator bbit = f->begin(), bbie = f->end(); bbit != bbie; ++bbit) {
        BasicBlock *bb = static_cast<BasicBlock *>(bbit);
        if (bb != exit) {
          Instruction *i = bbit->getTerminator();
          if (i->getOpcode() == Instruction::Ret) {
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

  if (!module_fns.empty()) {
    vector<Value*> values;
    values.reserve(module_fns.size());
    for (auto fn : module_fns) {
      values.push_back((Value*) fn);
      user_fns.insert(fn);
    }
    MDNode *Node = MDNode::get(ctx, values);
    NamedMDNode *NMD = module->getOrInsertNamedMetadata("brt-klee.usr-fns");
    NMD->addOperand(Node);
  }
  if (!module_gbs.empty()) {
    vector<Value*> values;
    values.reserve(module_gbs.size());
    for (auto gb : module_gbs) {
      values.push_back((Value*) gb);
      user_gbs.insert(gb);
    }
    MDNode *Node = MDNode::get(ctx, values);
    NamedMDNode *NMD = module->getOrInsertNamedMetadata("brt-klee.usr-gbs");
    NMD->addOperand(Node);
  }

  if (ttrace != TraceType::invalid) {
    Type *int_type = Type::getInt32Ty(ctx);
    vector<Value*> values;
    values.push_back(ConstantInt::get(int_type, (unsigned) ttrace));
    MDNode *Node = MDNode::get(ctx, values);
    NamedMDNode *NMD = module->getOrInsertNamedMetadata("brt-klee.trace-type");
    NMD->addOperand(Node);
  }
}

void KModule::prepare() {

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
          string str = cast<MDString>(node->getOperand(0))->getString();
          if (!str.empty()) mapFnMarkers[fn] = std::stoi(str);
        }
        if (MDNode *node = inst->getMetadata(mdkind_bbID)) {
          string str = cast<MDString>(node->getOperand(0))->getString();
          if (!str.empty()) mapBBMarkers[bb] = std::stoi(str);
        }
      }
    }
  }

  // read out the user defined functions from metadata
  auto node = module->getNamedMetadata("brt-klee.usr-fns");
  if (node != nullptr && node->getNumOperands() > 0) {
    auto md = node->getOperand(0);
    for (unsigned idx = 0, end = md->getNumOperands(); idx < end; ++idx) {
      Value *v = md->getOperand(idx);
      if (Function *fn = dyn_cast<Function>(v)) {
        user_fns.insert(fn);
      }
    }
  }

  // and now the globals
  node = module->getNamedMetadata("brt-klee.usr-gbs");
  if (node != nullptr && node->getNumOperands() > 0) {
    auto md = node->getOperand(0);
    for (unsigned idx = 0, end = md->getNumOperands(); idx < end; ++idx) {
      Value *v = md->getOperand(idx);
      if (GlobalVariable *gb = dyn_cast<GlobalVariable>(v)) {
        user_gbs.insert(gb);
      }
    }
  }

  // check to see if a default trace type is set in the module
  node = module->getNamedMetadata("brt-klee.trace-type");
  if (node != nullptr && node->getNumOperands() > 0) {
    auto md = node->getOperand(0);
    Value *v = md->getOperand(0);
    if (ConstantInt *i = dyn_cast<ConstantInt>(v)) {
      module_trace = (TraceType) i->getZExtValue();
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

    if (fn->isDeclaration()) continue;

    KFunction *kf = new KFunction(fn, this);

    for (unsigned i=0; i<kf->numInstructions; ++i) {
      KInstruction *ki = kf->instructions[i];
      ki->info = &infos->getInfo(ki->inst);
    }

    functions.push_back(kf);
    functionMap.insert(make_pair(fn, kf));
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

pair<unsigned,unsigned> KModule::getMarker(const llvm::Function *fn, const llvm::BasicBlock *bb) {

  unsigned fnID = 0;
  unsigned bbID = 0;
  const auto itr_fn = mapFnMarkers.find(fn);
  if (itr_fn != mapFnMarkers.end()) {
    fnID = itr_fn->second;
    const auto itr_bb = mapBBMarkers.find(bb);
    if (itr_bb != mapBBMarkers.end()) {
      bbID = itr_bb->second;
    }
  }
  return make_pair(fnID, bbID);
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

KFunction::KFunction(llvm::Function *_function, KModule *km)
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
    diff_sig(false) {

  is_user = km->isUserFunction(function);
  fnID = km->getFunctionID(function);

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
