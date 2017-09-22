//===-- KModule.h -----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_PROGINFO_H
#define KLEE_PROGINFO_H

#include <map>
#include <set>
#include <vector>
#include <boost/core/noncopyable.hpp>

namespace klee {

class ProgInfoFunction : private boost::noncopyable {

public:
  ProgInfoFunction()  { }

  bool isConstParam(unsigned index) const    { return constParams.count(index) > 0; }
  void setConstParam(unsigned index)         { constParams.insert(index); }

  bool isGlobalInput(std::string name) const { return globalInputs.count(name) > 0; }
  void setGlobalInput(std::string name)      { globalInputs.insert(name); }

private:
  std::set<unsigned> constParams;
  std::set<std::string> globalInputs;
};


class ProgInfo : private boost::noncopyable {

public:
  ProgInfo()    { }

  bool isConstParam(std::string fn, unsigned index)        { return fnInfo[fn].isConstParam(index); }
  void setConstParam(std::string fn, unsigned index)       { fnInfo[fn].setConstParam(index); }

  bool isGlobalInput(std::string fn, std::string name)     { return fnInfo[fn].isGlobalInput(name); }
  void setGlobalInput(std::string fn, std::string name)    { fnInfo[fn].setGlobalInput(name); }

private:
  std::map<std::string,ProgInfoFunction> fnInfo;
};

} // End klee namespace

#endif
