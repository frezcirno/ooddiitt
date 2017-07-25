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

  bool isConstParam(unsigned index) const  { return constParams.count(index) > 0; }
  void setConstParam(unsigned index)       { constParams.insert(index); }

private:
  std::set<unsigned> constParams;
};


class ProgInfo : private boost::noncopyable {

public:
  ProgInfo()    { }

  bool isConstParam(std::string name, unsigned index)   { return fnInfo[name].isConstParam(index); }
  void setConstParam(std::string name, unsigned index)  { fnInfo[name].setConstParam(index); }

private:
  std::map<std::string,ProgInfoFunction> fnInfo;
};

} // End klee namespace

#endif
