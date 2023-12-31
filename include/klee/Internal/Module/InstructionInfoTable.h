//===-- InstructionInfoTable.h ----------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_LIB_INSTRUCTIONINFOTABLE_H
#define KLEE_LIB_INSTRUCTIONINFOTABLE_H

#include <map>
#include <string>
#include <set>

#include <boost/filesystem.hpp>
namespace fs=boost::filesystem;

namespace llvm {
  class Function;
  class Instruction;
  class Module; 
}

namespace klee {

class KFunction;

  /* Stores debug information for a KInstruction */
  struct InstructionInfo {
    unsigned id;
    const char *file;
    const char *dir;
    unsigned line;
    unsigned assemblyLine;

  public:
    InstructionInfo() : id(0), file(nullptr), dir(nullptr), line(0), assemblyLine(0) {};
    InstructionInfo(unsigned _id,
                    const char *_file,
                    const char *_dir,
                    unsigned _line,
                    unsigned _assemblyLine)
      : id(_id), 
        file(_file),
        dir(_dir),
        line(_line),
        assemblyLine(_assemblyLine) {
    }
  };

  class InstructionInfoTable {
//    std::string dummyString;
//    InstructionInfo dummyInfo;
    std::map<const llvm::Instruction*, InstructionInfo> infos;
    std::set<std::string> internedStrings;

  private:
    const char *internString(const std::string &s) {
      auto itr = internedStrings.insert(s);
      return (*itr.first).c_str();
    }

    bool getInstructionDebugInfo(const llvm::Instruction *I,
                                 std::string &File, std::string &Dir, unsigned &Line);

    fs::path relative_root;

  public:
    InstructionInfoTable() { relative_root = fs::current_path(); };
    virtual ~InstructionInfoTable() = default;

    void LoadTable(llvm::Module *m);
    void BuildTable(llvm::Module *m);

    unsigned getMaxID() const;
    const InstructionInfo &getInfo(const llvm::Instruction*) const;
    const InstructionInfo &getFunctionInfo(const llvm::Function*) const;
//    std::map<const llvm::Instruction *,InstructionInfo> &getInfos() { return infos; }
  };

}

#endif
