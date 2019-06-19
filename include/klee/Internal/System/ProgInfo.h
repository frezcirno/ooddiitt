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

  bool isGlobalInput(const std::string &name) const { return globalInputs.count(name) > 0; }
  void setGlobalInput(const std::string &name)      { globalInputs.insert(name); }

  bool isReachableFn(const std::string &name) const  { return reachableFns.count(name) > 0; }
  void setReachableFn(const std::string &name)       { reachableFns.insert(name); }
  const std::set<std::string> &getReachableFns() const { return reachableFns; }

  bool isOutput(const std::string &name) const  { return outputs.count(name) > 0; }
  void setOutput(const std::string &name)       { outputs.insert(name); }

  unsigned getFnID() const                   { return fnID; }
  void setFnID(unsigned id)                  { fnID = id; }

  const std::set<unsigned> &get_markers() const { return markers; }
  void add_marker(unsigned marker)              { markers.insert(marker); }

  const std::set<std::string> &get_m2m_paths() const { return m2m_paths; }
  void add_m2m_path(const std::string &path)         { m2m_paths.insert(path); }

private:
  std::set<unsigned> constParams;
  std::set<std::string> globalInputs;
  std::set<std::string> outputs;
  std::set<std::string> reachableFns;
  std::set<std::string> m2m_paths;
  std::set<unsigned> markers;
  unsigned fnID;
};

class ProgInfo : private boost::noncopyable {

public:
  ProgInfo()    { }

  bool empty()  { return fnInfo.empty(); }

  bool isConstParam(const std::string &fn, unsigned index) const
    { auto itr = fnInfo.find(fn); return (itr != fnInfo.end() ? itr->second.isConstParam(index) : false); }
  void setConstParam(std::string fn, unsigned index)       { fnInfo[fn].setConstParam(index); }

  bool isGlobalInput(const std::string &fn, std::string name) const
    { auto itr = fnInfo.find(fn); return (itr != fnInfo.end() ? itr->second.isGlobalInput(name) : false); }
  void setGlobalInput(std::string fn, std::string name)      { fnInfo[fn].setGlobalInput(name); }

  bool isReachableFn(const std::string &fn, std::string name) const
    { auto itr = fnInfo.find(fn); return (itr != fnInfo.end() ? itr->second.isReachableFn(name) : false); }
  void setReachableFn(std::string fn, std::string name)      { fnInfo[fn].setReachableFn(name); }

  bool isOutput(const std::string &fn, std::string name) const
    { auto itr = fnInfo.find(fn); return (itr != fnInfo.end() ? itr->second.isOutput(name) : false); }
  void setOutput(std::string fn, std::string name)      { fnInfo[fn].setOutput(name); }

  bool isReachableOutput(const std::string &fn, std::string name) const {
    const auto &fn_itr = fnInfo.find(fn);
    if (fn_itr != fnInfo.end()) {
      for (const auto &item : fn_itr->second.getReachableFns()) {
        auto child_itr = fnInfo.find(item);
        if (child_itr != fnInfo.end()) {
          if (child_itr->second.isOutput(name)) return true;
        }
      }
    }
    return false;
  }

  unsigned getFnID(const std::string &fn) const
    { auto itr = fnInfo.find(fn); return (itr != fnInfo.end() ? itr->second.getFnID() : 0); }
  void setFnID(std::string fn, unsigned id)                { fnInfo[fn].setFnID(id); }

  const std::set<unsigned> *get_markers(const std::string &fn) const
    { auto itr = fnInfo.find(fn); return (itr != fnInfo.end() ? &itr->second.get_markers() : nullptr); }
  void add_marker(std::string fn, unsigned marker)            { fnInfo[fn].add_marker(marker); }

  const std::set<std::string> *get_m2m_paths(const std::string &fn) const
    { auto itr = fnInfo.find(fn); return (itr != fnInfo.end() ? &itr->second.get_m2m_paths() : nullptr); }
  void add_m2m_path(std::string fn, std::string path)              { fnInfo[fn].add_m2m_path(path); }

private:
  std::map<std::string,ProgInfoFunction> fnInfo;
};

} // End klee namespace

#endif
