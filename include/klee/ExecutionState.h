//===-- ExecutionState.h ----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXECUTIONSTATE_H
#define KLEE_EXECUTIONSTATE_H

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/Internal/ADT/TreeStream.h"

// FIXME: We do not want to be exposing these? :(
#include "../../lib/Core/AddressSpace.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KInstIterator.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/util/CommonUtil.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Module.h"

#include <map>
#include <set>
#include <vector>

#define INVALID_BB_INDEX  ((unsigned) -1)

namespace klee {
class Array;
class CallPathNode;
struct Cell;
struct KFunction;
struct KInstruction;
class MemoryObject;
class PTreeNode;
struct InstructionInfo;

llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const MemoryMap &mm);

class ProgramTracer {

public:
  ProgramTracer() = default;
  virtual ~ProgramTracer() = default;
  void append(TraceDequeT &trace, const char *str, unsigned entry, bool force=false) {
      if (
          (entry != 0) &&
          (force || trace.empty() || (trace.back().first != str) || (trace.back().second != entry))
         ) trace.emplace_back(str, entry); }
  void append(TraceDequeT &trace, unsigned entry, bool force=false) {
    if (
        (entry != 0) &&
        (force || trace.empty() || (trace.back().second != entry))
       ) trace.emplace_back(nullptr, entry); }
  virtual void append_instr(TraceDequeT &trace, KInstruction *ki) {}
  virtual void append_call(TraceDequeT &trace, const KFunction *kf) {}
  virtual void append_return(TraceDequeT &trace, const KFunction *kf) {}
};

class AssemblyTracer : public ProgramTracer {
public:
  void append_instr(TraceDequeT &trace, KInstruction *ki) override  {
    append(trace, ki->info->assemblyLine);
  }
};

class StatementTracer : public ProgramTracer {
public:
  void append_instr(TraceDequeT &trace, KInstruction *ki) override  {
    append(trace, ki->info->file, ki->info->line);
  }
};

class BBlocksTracer : public ProgramTracer {
public:
  explicit BBlocksTracer(KModule *k) : kmodule(k)  { }

  void append_instr(TraceDequeT &trace, KInstruction *ki) override  {
    llvm::BasicBlock *bb = ki->inst->getParent();
    llvm::Function *fn = bb->getParent();
    auto pr = kmodule->getMarker(fn, bb);
    if (pr.second != 0) {
      KFunction *kf = kmodule->getKFunction(fn);
      append(trace, kf->getName().c_str(), pr.second);
    }
  }
private:
  KModule *kmodule;
};

class CallTracer : public ProgramTracer {
public:
  explicit CallTracer(KModule *k) : kmodule(k)  {}
  void append_call(TraceDequeT &trace, const KFunction *kf) override {
    append(trace, kf->getName().c_str(), 1, true);
  }

  void append_return(TraceDequeT &trace, const KFunction *kf) override {
    append(trace, kf->getName().c_str(), 2, true);
  }

private:
  KModule *kmodule;
};

struct LoopFrame {
  const llvm::Loop *loop;
  unsigned counter;

  explicit LoopFrame(const llvm::Loop *l) : loop(l), counter(0) {};
  LoopFrame(const LoopFrame &s) : loop(s.loop), counter(s.counter) {};
  ~LoopFrame() = default;
};

struct StackFrame {
  KInstIterator caller;
  KFunction *kf;
#ifdef _DEBUG
  std::string fn_name;
#endif  // _DEBUG
  CallPathNode *callPathNode;
  std::set<const MemoryObject *> allocas;
  size_t numRegs;
  Cell *locals;

  std::vector<LoopFrame> loopFrames;

  /// Minimum distance to an uncovered instruction once the function
  /// returns. This is not a good place for this but is used to
  /// quickly compute the context sensitive minimum distance to an
  /// uncovered instruction. This value is updated by the StatsTracker
  /// periodically.
  unsigned minDistToUncoveredOnReturn;

  // For vararg functions: arguments not passed via parameter are
  // stored (packed tightly) in a local (alloca) memory object. This
  // is setup to match the way the front-end generates vaarg code (it
  // does not pass vaarg through as expected). VACopy is lowered inside
  // of intrinsic lowering.
  MemoryObject *varargs;

  StackFrame(KInstIterator caller, KFunction *kf);
  StackFrame(const StackFrame &s);
  ~StackFrame();
};

class CharacterOutput : public std::deque<std::vector<unsigned char> > {
public:

  size_t accum_size() const {
    size_t size = 0;
    for (const auto &v : *this) {
      size += v.size();
    }
    return size;
  }

  void get_data(std::vector<unsigned char> &data) const {
    data.clear();
    // two iterations, one just collect size, the other to insert data
    data.reserve(accum_size());
    for (const auto &v : *this) {
      data.insert(data.end(), v.begin(), v.end());
    }
  }

};

/// @brief ExecutionState representing a path under exploration
class ExecutionState {
public:
  typedef std::vector<StackFrame> stack_ty;

private:
  // unsupported, use copy constructor
  ExecutionState &operator=(const ExecutionState &);
  std::map<std::string, std::string> fnAliases;

public:

  void restartInstruction() { pc = prevPC; }

  // Execution - Control Flow specific

  /// @brief Pointer to instruction to be executed after the current
  /// instruction
  KInstIterator pc;

  /// @brief Pointer to instruction which is currently executed
  KInstIterator prevPC;

  /// @brief Stack representing the current instruction stream
  stack_ty stack;

  /// @brief Remember from which Basic Block control flow arrived
  /// (i.e. to select the right phi values)
  unsigned incomingBBIndex;

  // Overall state of the state - Data specific

  /// @brief Address space used by this state (e.g. Global and Heap)
  AddressSpace addressSpace;

  /// @brief Constraints collected so far
  ConstraintManager constraints;

  /// Statistics and information

  /// @brief Costs for all queries issued for this state, in seconds
  mutable double queryCost;

  /// @brief Weight assigned for importance of this state.  Can be
  /// used for searchers to decide what paths to explore
  double weight;

  /// @brief Exploration depth, i.e., number of times KLEE branched for this state
  unsigned depth;

  /// @brief History of complete path: represents branches taken to
  /// reach/create this state (both concrete and symbolic)
  TreeOStream pathOS;

  /// @brief History of symbolic path: represents symbolic branches
  /// taken to reach/create this state
  TreeOStream symPathOS;

  /// @brief Counts how many instructions were executed since the last new
  /// instruction was covered.
  unsigned instsSinceCovNew;

  /// @brief Whether a new instruction was covered in this state
  bool coveredNew;

  /// @brief Disables forking for this state. Set by user code
  bool forkDisabled;

  /// @brief Set containing which lines in which files are covered by this state
  std::map<const char*, std::set<unsigned> > coveredLines;

  /// @brief Pointer to the process tree of the current state
  PTreeNode *ptreeNode;

  /// @brief Ordered list of symbolics: used to generate test cases.
  //
  // FIXME: Move to a shared list structure (not critical).
  std::vector<std::pair<const MemoryObject *, const Array *> > symbolics;

  /// @brief Set of used array names for this state.  Used to avoid collisions.
  std::set<std::string> arrayNames;

  std::map<llvm::Function*,unsigned> callTargetCounter;

  std::string name;
  bool isProcessed;

  unsigned lazyAllocationCount;
  unsigned lazyStringLength;
  unsigned maxLazyDepth;
  unsigned maxStatesInLoop;

  StateStatus status;
  std::deque<std::string> messages;
  const KInstruction *instFaulting;
  uint64_t addrFaulting;
  const MemoryObject *moFaulting;
  std::deque<std::pair<const char *,unsigned>> trace;
  std::vector<ref<Expr> > arguments;
  unsigned allBranchCounter;
  unsigned unconBranchCounter;
  const KInstruction* branched_at;

  CharacterOutput stdout_capture;
  CharacterOutput stderr_capture;
  unsigned stdin_offset;
  bool stdin_closed;
  std::vector<unsigned char> stdin_buffer;
  unsigned eof_counter;

  ref<Expr> last_ret_value;
  unsigned min_distance;
  unsigned linear_distance;

  bool reached_target;
  std::deque<std::pair<unsigned, KInstruction *>> o_asserts;
  std::map<const llvm::Function *, std::string> bound_fnptrs;

  std::string getFnAlias(std::string fn);
  void addFnAlias(std::string old_fn, std::string new_fn);
  void removeFnAlias(std::string fn);

  ExecutionState(); // : ptreeNode(0) {}
  ExecutionState(const ExecutionState &state, KFunction *kf, const std::string &name);

  // XXX total hack, just used to make a state so solver can
  // use on structure
  ExecutionState(const ExecutionState &state, const std::vector<ref<Expr> > &assumptions);

  ExecutionState(const ExecutionState &state);

  ~ExecutionState();

  ExecutionState *branch();

  void pushFrame(KInstIterator caller, KFunction *kf);
  void popFrame();
  const llvm::Loop *getTopMostLoop() const;
  bool getAllLoops(std::set<const llvm::Loop *> &loops) const;

  void addSymbolic(const MemoryObject *mo, const Array *array);
  bool isSymbolic(const MemoryObject *mo) const { return findSymbolic(mo) != nullptr; }
  const Array *findSymbolic(const MemoryObject *mo) const {
    for (auto &pr : symbolics) {
      if (pr.first==mo) {
        return pr.second;
      }
    }
    return nullptr;
  }
  bool isConcrete(const MemoryObject *mo);
  void addConstraint(ref<Expr> e)   { constraints.addConstraint(e); }

  bool merge(const ExecutionState &b);
  void dumpStack(llvm::raw_ostream &out) const;
};
}

#endif
