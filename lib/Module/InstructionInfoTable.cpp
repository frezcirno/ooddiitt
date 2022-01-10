//===-- InstructionInfoTable.cpp ------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Config/Version.h"
#include "MDBuilder.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#else
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#endif

# if LLVM_VERSION_CODE < LLVM_VERSION(3,5)
#include "llvm/Assembly/AssemblyAnnotationWriter.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Linker.h"
#else
#include "llvm/IR/AssemblyAnnotationWriter.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Linker/Linker.h"
#endif

#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/raw_ostream.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3,5)
#include "llvm/IR/DebugInfo.h"
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
#include "llvm/DebugInfo.h"
#else
#include "llvm/Analysis/DebugInfo.h"
#endif

#include "llvm/Support/ErrorHandling.h"

#include <map>
#include <string>
#include <klee/Internal/Support/ErrorHandling.h>
//#include <boost/filesystem.hpp>

using namespace llvm;
using namespace klee;
//namespace fs=boost::filesystem;

class InstructionToLineAnnotator : public llvm::AssemblyAnnotationWriter {
public:
  void emitInstructionAnnot(const Instruction *i, llvm::formatted_raw_ostream &os) override {
    os << "%%%";
    os << (uintptr_t) i;
  }
};

static void buildInstructionToLineMap(Module *m, std::map<const Instruction*, unsigned> &out) {
  InstructionToLineAnnotator a;
  std::string str;
  llvm::raw_string_ostream os(str);
  m->print(os, &a);
  os.flush();
  const char *s;

  unsigned line = 1;
  for (s=str.c_str(); *s; s++) {
    if (*s=='\n') {
      line++;
      if (s[1]=='%' && s[2]=='%' && s[3]=='%') {
        s += 4;
        char *end;
        unsigned long long value = strtoull(s, &end, 10);
        if (end!=s) {
          out.insert(std::make_pair((const Instruction*) value, line));
        }
        s = end;
      }
    }
  }
}

//static void getDSPIPath(DILocation Loc, fs::path &file, fs::path &dir) {

  //  fs::path pdir(Loc.getDirectory());
  //  fs::path pfile(Loc.getFilename());
  //  fs::path pfull = pdir/pfile;
//  dir = Loc.getDirectory();
//  file = Loc.getFilename();
//  file = pfull.filename().string();
//}

bool InstructionInfoTable::getInstructionDebugInfo(const llvm::Instruction *I, std::string &File, std::string &Dir, unsigned &Line) {

  if (MDNode *N = I->getMetadata("dbg")) {
    DILocation Loc(N);
//    fs::path f, p;
//    getDSPIPath(Loc, f, p);
    File = Loc.getFilename();
    Dir = fs::relative(fs::path(Loc.getDirectory()), relative_root).string();
    Line = Loc.getLineNumber();
    return true;
  }
  return false;
}

void InstructionInfoTable::BuildTable(llvm::Module *m) {

  llvm::LLVMContext &ctx = m->getContext();
  MDBuilder md_builder(ctx);
  unsigned int mdkline = m->getMDKindID("klee.assemblyLine");
  unsigned id = 0;

  std::map<const Instruction*, unsigned> lineTable;
  buildInstructionToLineMap(m, lineTable);

  for (auto fn_it = m->begin(), fn_ie = m->end(); fn_it != fn_ie; ++fn_it) {

    // We want to ensure that as all instructions have source information, if
    // available. Clang sometimes will not write out debug information on the
    // initial instructions in a function (correspond to the formal parameters),
    // so we first search forward to find the first instruction with debug info,
    // if any.
    const char *file = "na";
    const char *dir = "na";
    unsigned line = 0;
    for (auto inst_it = inst_begin(fn_it), inst_ie = inst_end(fn_it); inst_it != inst_ie; ++inst_it) {
      Instruction *instr = &*inst_it;
      std::string tmp_file, tmp_dir;
      if (getInstructionDebugInfo(instr, tmp_file, tmp_dir, line)) {
        file = internString(tmp_file);
        dir = internString(tmp_dir);
        break;
      }
    }

    // start over, using the first found debug values from above
    for (auto inst_it = inst_begin(fn_it), inst_ie = inst_end(fn_it); inst_it != inst_ie; ++inst_it) {
      Instruction *instr = &*inst_it;
      unsigned assemblyLine = lineTable[instr];
      std::string tmp_file, tmp_dir;

      // Update our source level debug information.
      if (getInstructionDebugInfo(instr, tmp_file, tmp_dir, line)) {
        file = internString(tmp_file);
        dir = internString(tmp_dir);
      }

      MDNode *N = md_builder.create(assemblyLine);
      instr->setMetadata(mdkline, N);
      infos.insert(std::make_pair(instr, InstructionInfo(id++, file, dir, line, assemblyLine)));
    }
  }
}

void InstructionInfoTable::LoadTable(llvm::Module *m) {

  unsigned int mdkline = m->getMDKindID("klee.assemblyLine");
  unsigned id = 0;

  for (auto fn_it = m->begin(), fn_ie = m->end(); fn_it != fn_ie; ++fn_it) {

    // We want to ensure that as all instructions have source information, if
    // available. Clang sometimes will not write out debug information on the
    // initial instructions in a function (correspond to the formal parameters),
    // so we first search forward to find the first instruction with debug info,
    // if any.
    const char *file = nullptr;
    const char *path = nullptr;
    unsigned line = 0;
    for (auto inst_it = inst_begin(fn_it), inst_ie = inst_end(fn_it); inst_it != inst_ie; ++inst_it) {
      Instruction *instr = &*inst_it;
      std::string tmp_file, tmp_path;
      if (getInstructionDebugInfo(instr, tmp_file, tmp_path, line)) {
        file = internString(tmp_file);
        path = internString(tmp_path);
        break;
      }
    }

    // start over, using the first found debug values from above
    for (auto inst_it = inst_begin(fn_it), inst_ie = inst_end(fn_it); inst_it != inst_ie; ++inst_it) {
      Instruction *instr = &*inst_it;
      std::string tmp_file, tmp_path;

      // Update our source level debug information.
      if (getInstructionDebugInfo(instr, tmp_file, tmp_path, line)) {
        file = internString(tmp_file);
        path = internString(tmp_path);
      }
      unsigned assemblyLine = 0;
      if (MDNode *node = instr->getMetadata(mdkline)) {
        if (ConstantInt *vi = dyn_cast<ConstantInt>(node->getOperand(0))) {
         assemblyLine = vi->getZExtValue();
        }
      }
      infos.insert(std::make_pair(instr, InstructionInfo(id++, file, path, line, assemblyLine)));
    }
  }
}

unsigned InstructionInfoTable::getMaxID() const {
  return infos.size();
}

const InstructionInfo &InstructionInfoTable::getInfo(const Instruction *inst) const {
  auto itr = infos.find(inst);
  if (itr == infos.end()) {
    klee_error("invalid instruction, not present in initial module!");
  }
  return itr->second;
}

const InstructionInfo &InstructionInfoTable::getFunctionInfo(const Function *f) const {

  if (f->isDeclaration()) {

    static InstructionInfo dummyInfo;
    // FIXME: We should probably eliminate this dummyInfo object, and instead
    // allocate a per-function object to track the stats for that function
    // (otherwise, anyone actually trying to use those stats is getting ones
    // shared across all functions). I'd like to see if this matters in practice
    // and construct a test case for it if it does, though.
    return dummyInfo;
  } else {
    return getInfo(f->begin()->begin());
  }
}
