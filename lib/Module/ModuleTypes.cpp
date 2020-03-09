//===-- ModuleTypes.cpp - Implement the ModuleTypes class -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the ModuleTypes class for the IR library.
// This class only exists because llvm-3.4 TypeFinder is throwing an exception
//
//===----------------------------------------------------------------------===//

#include "klee/Internal/Module/ModuleTypes.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"

using namespace llvm;
using namespace std;

namespace klee {

bool ModuleTypes::get(std::set<llvm::StructType*> &types) {

  set<Type*> all_types;
  get(all_types);
  for (Type *type : all_types) {
    if (StructType *st = dyn_cast<StructType>(type)) {
      types.insert(st);
    }
  }
  return !types.empty();
}

bool ModuleTypes::get(std::set<llvm::Type*> &types) {

  types.clear();

  // Get types from global variables.
  for (auto itr = module->global_begin(), end = module->global_end(); itr != end; ++itr) {
    incorporateType(itr->getType(), types);
    if (itr->hasInitializer())
      incorporateValue(itr->getInitializer(), types);
  }

  // Get types from aliases.
  for (auto itr = module->alias_begin(), end = module->alias_end(); itr != end; ++itr) {
    incorporateType(itr->getType(), types);
    if (const Value *Aliasee = itr->getAliasee())
      incorporateValue(Aliasee, types);
  }

  // Get types from functions.
  SmallVector<pair<unsigned, MDNode*>, 4> MDForInst;
  for (auto fn_itr = module->begin(), fn_end = module->end(); fn_itr != fn_end; ++fn_itr) {
    incorporateType(fn_itr->getType(), types);

    if (fn_itr->hasPrefixData())
      incorporateValue(fn_itr->getPrefixData(), types);

    // First incorporate the arguments.
    for (auto arg_itr = fn_itr->arg_begin(), arg_end = fn_itr->arg_end(); arg_itr != arg_end; ++arg_itr) {
      incorporateValue(arg_itr, types);
    }

    for (auto bb_itr = fn_itr->begin(), bb_end = fn_itr->end(); bb_itr != bb_end; ++bb_itr) {
      for (auto inst_itr = bb_itr->begin(), inst_end = bb_itr->end(); inst_itr != inst_end; ++inst_end) {
        const Instruction &I = *inst_itr;

        // Incorporate the type of the instruction.
        incorporateType(I.getType(), types);

        // Incorporate non-instruction operand types. (We are incorporating all
        // instructions with this loop.)
        for (auto op_itr = I.op_begin(), op_end = I.op_end(); op_itr != op_end; ++op_itr) {
          if (!isa<Instruction>(op_itr)) {
            incorporateValue(*op_itr, types);
          }
        }

        // Incorporate types hiding in metadata.
        I.getAllMetadataOtherThanDebugLoc(MDForInst);
        for (unsigned idx = 0, end = MDForInst.size(); idx != end; ++idx) {
          incorporateMDNode(MDForInst[idx].second, types);
        }
        MDForInst.clear();
      }
    }
  }

  for (auto itr = module->named_metadata_begin(), end = module->named_metadata_end(); itr != end; ++itr) {
    const NamedMDNode *NMD = itr;
    for (unsigned i = 0, e = NMD->getNumOperands(); i != e; ++i) {
      incorporateMDNode(NMD->getOperand(i), types);
    }
  }
  return !types.empty();
}

/// incorporateType - This method adds the type to the list of used structures
/// if it's not in there already.

void ModuleTypes::incorporateType(Type *Ty, std::set<llvm::Type*> &types) {
  // Check to see if we've already visited this type.
  if (!VisitedTypes.insert(Ty).second)
    return;

//  SmallVector<Type *, 4> TypeWorklist;
//  TypeWorklist.push_back(Ty);
  vector<Type*> worklist;
  worklist.push_back(Ty);
  do {
    Type *type = worklist.back();
    worklist.pop_back();

    // If this is a structure or opaque type, add a name for the type.
    if (StructType *STy = dyn_cast<StructType>(type)) {
      types.insert(STy);
    }

    // Add all unvisited subtypes to worklist for processing
    for (auto itr = type->subtype_rbegin(), end = type->subtype_rend(); itr != end; ++itr) {
      Type *subtype = *itr;
      if (VisitedTypes.insert(subtype).second)
        worklist.push_back(subtype);
    }
  } while (!worklist.empty());
}

/// incorporateValue - This method is used to walk operand lists finding types
/// hiding in constant expressions and other operands that won't be walked in
/// other ways.  GlobalValues, basic blocks, instructions, and inst operands are
/// all explicitly enumerated.
void ModuleTypes::incorporateValue(const Value *V, std::set<llvm::Type*> &types) {

  if (const MDNode *M = dyn_cast<MDNode>(V)) {
    return incorporateMDNode(M, types);
  }

  if (!isa<Constant>(V) || isa<GlobalValue>(V))
    return;

  // Already visited?
  if (!VisitedConstants.insert(V).second)
    return;

  // Check this type.
  incorporateType(V->getType(), types);

  // If this is an instruction, we incorporate it separately.
  if (isa<Instruction>(V))
    return;

  // Look in operands for types.
  const User *U = cast<User>(V);
  for (auto itr = U->op_begin(), end = U->op_end(); itr != end; ++itr) {
    incorporateValue(*itr, types);
  }
}

/// incorporateMDNode - This method is used to walk the operands of an MDNode to
/// find types hiding within.
void ModuleTypes::incorporateMDNode(const MDNode *V, std::set<llvm::Type*> &types) {
  // Already visited?
  if (!VisitedConstants.insert(V).second)
    return;

  // Look in operands for types.
  for (unsigned idx = 0, end = V->getNumOperands(); idx != end; ++idx) {
    if (Value *Op = V->getOperand(idx)) {
      incorporateValue(Op, types);
    }
  }
}

} // namespace klee
