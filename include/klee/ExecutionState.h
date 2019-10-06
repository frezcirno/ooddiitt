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
#include "klee/Internal/Module/KInstIterator.h"
#include "klee/Internal/Module/KModule.h"
#include "llvm/IR/BasicBlock.h"

#include <map>
#include <set>
#include <vector>

//#define INVALID_LOOP_SIGNATURE   (0)
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

struct LoopFrame {
  const llvm::Loop *loop;
  unsigned counter;

  LoopFrame(const llvm::Loop *l) : loop(l), counter(0) {}
  LoopFrame(const LoopFrame &s) : loop(s.loop), counter(s.counter) {}
};

struct StackFrame {
  KInstIterator caller;
  KFunction *kf;
  CallPathNode *callPathNode;

  std::set<const MemoryObject *> allocas;
  size_t numRegs;
  Cell *locals;

  std::vector<LoopFrame> loopFrames;
  std::deque<unsigned> itrace;

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

/// @brief ExecutionState representing a path under exploration
class ExecutionState {
public:
  // RLR TODO: evaluate if this should really be a vector
  typedef std::vector<StackFrame> stack_ty;

private:
  // unsupported, use copy constructor
  ExecutionState &operator=(const ExecutionState &);

  std::map<std::string, std::string> fnAliases;
//  static unsigned long lastUsedStateSignature;

public:

  enum StateStatus {
    Pending,
    Completed,
    Faulted,
    TerminateEarly,
    TerminateError,
    Decimated,
    TerminateDiscard
  };

  std::string get_status() const {
    std::string result = "unknown";
    switch (status) {
    case Pending: result = "pending"; break;
    case Completed: result = "completed"; break;
    case Faulted: result = "faulted"; break;
    case TerminateEarly: result = "early"; break;
    case TerminateError: result = "error"; break;
    case Decimated: result = "decimate"; break;
    case TerminateDiscard: result = "discard"; break;
    }
    return result;
  }

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
  std::map<const std::string *, std::set<unsigned> > coveredLines;

  /// @brief Pointer to the process tree of the current state
  PTreeNode *ptreeNode;

  /// @brief Ordered list of symbolics: used to generate test cases.
  //
  // FIXME: Move to a shared list structure (not critical).
  std::vector<std::pair<const MemoryObject *, const Array *> > symbolics;

  /// @brief Set of used array names for this state.  Used to avoid collisions.
  std::set<std::string> arrayNames;

  std::map<std::string, unsigned> callTargetCounter;

  std::string name;
  bool isProcessed;
  bool isInteresting;
  unsigned lazyAllocationCount;
  unsigned maxLoopIteration;
  unsigned maxLoopForks;
  unsigned maxLazyDepth;
  StateStatus status;
  std::string terminationMessage;
  const KInstruction *instFaulting;
  unsigned startingMarker;
  unsigned endingMarker;
  std::deque<std::pair<unsigned,unsigned> > trace;
  M2MPaths itraces;
  M2MPaths selected_paths;
  unsigned allBranchCounter;
  unsigned unconBranchCounter;
  const KInstruction* branched_at;

  std::string getFnAlias(std::string fn);
  void addFnAlias(std::string old_fn, std::string new_fn);
  void removeFnAlias(std::string fn);

  ExecutionState(void *base_addr); // : ptreeNode(0) {}
  ExecutionState(const ExecutionState &state, KFunction *kf, const std::string &name);

  // XXX total hack, just used to make a state so solver can
  // use on structure
  ExecutionState(const ExecutionState &state, const std::vector<ref<Expr> > &assumptions);

  ExecutionState(const ExecutionState &state);

  ~ExecutionState();

  ExecutionState *branch();

  void pushFrame(KInstIterator caller, KFunction *kf);
  void popFrame();
  void extractITrace(StackFrame &frame);

  void addSymbolic(const MemoryObject *mo, const Array *array);
  bool isSymbolic(const MemoryObject *mo);
  bool isConcrete(const MemoryObject *mo);
  void addMarker(unsigned fnID, unsigned bbID);

  void addConstraint(ref<Expr> e)   { constraints.addConstraint(e); }

  bool merge(const ExecutionState &b);
  void dumpStack(llvm::raw_ostream &out) const;
};
}

#endif
