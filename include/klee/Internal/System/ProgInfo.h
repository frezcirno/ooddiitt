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
  ProgInfoFunction() : fnID(0)  { }

  bool isConstParam(unsigned index) const    { return constParams.count(index) > 0; }
  void setConstParam(unsigned index)         { constParams.insert(index); }

  bool isGlobalInput(std::string name) const { return globalInputs.count(name) > 0; }
  void setGlobalInput(std::string name)      { globalInputs.insert(name); }

  bool isReachableOutput(std::string name) const  { return reachableOutputs.count(name) > 0; }
  void setReachableOutput(std::string name)       { reachableOutputs.insert(name); }

  unsigned getFnID() const                   { return fnID; }
  void setFnID(unsigned id)                  { fnID = id; }

private:
  std::set<unsigned> constParams;
  std::set<std::string> globalInputs;
  std::set<std::string> reachableOutputs;
  unsigned fnID;
};


class ProgInfo : private boost::noncopyable {

public:
  ProgInfo()    { }

  bool isConstParam(std::string fn, unsigned index)        { return fnInfo[fn].isConstParam(index); }
  void setConstParam(std::string fn, unsigned index)       { fnInfo[fn].setConstParam(index); }

  bool isGlobalInput(std::string fn, std::string name)     { return fnInfo[fn].isGlobalInput(name); }
  void setGlobalInput(std::string fn, std::string name)    { fnInfo[fn].setGlobalInput(name); }

  bool isReachableOutput(std::string fn, std::string name)  { return fnInfo[fn].isReachableOutput(name); }
  void setReachableOutput(std::string fn, std::string name)  { fnInfo[fn].setReachableOutput(name); }

  unsigned getFnID(std::string fn)                         { return fnInfo[fn].getFnID(); }
  void setFnID(std::string fn, unsigned id)                { fnInfo[fn].setFnID(id); }

private:
  std::map<std::string,ProgInfoFunction> fnInfo;
};

} // End klee namespace

#endif
