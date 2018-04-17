//===-- Memory.h ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_MEMORY_H
#define KLEE_MEMORY_H

#include "../../../../lib/Core/Context.h"
#include "klee/Expr.h"

#include "llvm/ADT/StringExtras.h"

#include <vector>
#include <string>

namespace llvm {
  class Value;
}

namespace klee {

class BitArray;
class MemoryManager;
class Solver;
class ArrayCache;

enum MemKind { invalid, fixed, global, param, alloca, heap, output, lazy };

class MemoryObject {
  friend class STPBuilder;
  friend class ObjectState;
  friend class ExecutionState;

private:
  static unsigned counter;
  mutable unsigned refCount;

public:

  unsigned id;
  uint64_t address;

  /// size in bytes
  unsigned size;
  mutable unsigned visible_size;
  size_t align;
  mutable std::string name;

  MemKind kind;
  const llvm::Type *type;
  unsigned count;

  /// true if created by us.
  bool fake_object;
  bool isUserSpecified;

  MemoryManager *parent;

  /// "Location" for which this memory object was allocated. This
  /// should be either the allocating instruction or the global object
  /// it was allocated for (or whatever else makes sense).
  const llvm::Value *allocSite;
  
  /// A list of boolean expressions the user has requested be true of
  /// a counterexample. Mutable since we play a little fast and loose
  /// with allowing it to be added to during execution (although
  /// should sensibly be only at creation time).
  mutable std::vector< ref<Expr> > cexPreferences;

  // DO NOT IMPLEMENT
  MemoryObject(const MemoryObject &b);
  MemoryObject &operator=(const MemoryObject &b);

public:
  // XXX this is just a temp hack, should be removed
  explicit
  MemoryObject(uint64_t _address) 
    : refCount(0),
      id(counter++), 
      address(_address),
      size(0),
      visible_size(0),
      name("hack"),
      kind(MemKind::fixed),
      type(nullptr),
      count(0),
      parent(NULL),
      allocSite(0) {
  }

  MemoryObject(uint64_t _address, unsigned _size, size_t _align,
               const llvm::Type *type, MemKind _kind,
               const llvm::Value *_allocSite, MemoryManager *_parent)
    : refCount(0), 
      id(counter++),
      address(_address),
      size(_size),
      visible_size(_size),
      align(_align),
      name(""),
      kind(_kind),
      type(type),
      count(0),
      fake_object(false),
      isUserSpecified(false),
      parent(_parent), 
      allocSite(_allocSite) {
  }

  bool isValid() const  { return kind != MemKind::invalid; }
  bool isFixed() const  { return kind == MemKind::fixed; }
  bool isGlobal() const { return kind == MemKind::global; }
  bool isParam() const  { return kind == MemKind::param; }
  bool isAlloca() const { return kind == MemKind::alloca; }
  bool isHeap() const   { return kind == MemKind::heap; }
  bool isOutput() const { return kind == MemKind::output; }
  bool isLazy() const   { return kind == MemKind::lazy; }
  bool isLocal() const  { return (kind == MemKind::param) || (kind == MemKind::alloca); }

  const char *getKindAsStr() const
    {
      static const char* kindStrings[] = {"invalid", "fixed", "global", "param", "alloca", "heap", "output", "lazy"};
      return kindStrings[kind];
    };

  ~MemoryObject();

  /// Get an identifying string for this allocation.
  void getAllocInfo(std::string &result) const;

  ref<ConstantExpr> getBaseExpr() const {
    return ConstantExpr::create(address, Context::get().getPointerWidth());
  }
  ref<ConstantExpr> getSizeExpr() const { 
    return ConstantExpr::create(visible_size, Context::get().getPointerWidth());
  }
  ref<Expr> getOffsetExpr(ref<Expr> pointer) const {
    return SubExpr::create(pointer, getBaseExpr());
  }
  ref<Expr> getBoundsCheckPointer(ref<Expr> pointer) const {
    return getBoundsCheckOffset(getOffsetExpr(pointer));
  }
  ref<Expr> getBoundsCheckPointer(ref<Expr> pointer, unsigned bytes) const {
    return getBoundsCheckOffset(getOffsetExpr(pointer), bytes);
  }

  ref<Expr> getBoundsCheckOffset(ref<Expr> offset) const {
    if (visible_size==0) {
      return EqExpr::create(offset, 
                            ConstantExpr::alloc(0, Context::get().getPointerWidth()));
    } else {
      return UltExpr::create(offset, getSizeExpr());
    }
  }
  ref<Expr> getBoundsCheckOffset(ref<Expr> offset, unsigned bytes) const {
    if (bytes<=visible_size) {
      return UltExpr::create(offset, 
                             ConstantExpr::alloc(visible_size - bytes + 1,
                                                 Context::get().getPointerWidth()));
    } else {
      return ConstantExpr::alloc(0, Expr::Bool);
    }
  }
};

class ObjectState {
private:
  friend class AddressSpace;
  unsigned copyOnWriteOwner; // exclusively for AddressSpace

  friend class ObjectHolder;
  unsigned refCount;

  const MemoryObject *object;

  uint8_t *concreteStore;
  // XXX cleanup name of flushMask (its backwards or something)
  BitArray *concreteMask;

  // mutable because may need flushed during read of const
  mutable BitArray *flushMask;

  ref<Expr> *knownSymbolics;

  // mutable because we may need flush during read of const
  mutable UpdateList updates;
  
  BitArray *writtenMask;

public:
    //RLR TODO: evaluate whether symboliclyWritten is still needed.
  bool symboliclyWritten;
//  unsigned visible_size;
  bool readOnly;

public:

  /// Create a new object state for the given memory object with concrete
  /// contents. The initial contents are undefined, it is the callers
  /// responsibility to initialize the object contents appropriately.
  ObjectState(const MemoryObject *mo);

  /// Create a new object state for the given memory object with symbolic
  /// contents.
  ObjectState(const MemoryObject *mo, const Array *array);

  ObjectState(const ObjectState &os);
  ~ObjectState();

  const MemoryObject *getObject() const { return object; }

  void setReadOnly(bool ro) { readOnly = ro; }

  // make contents all concrete and zero
  void initializeToZero();
  // make contents all concrete and random
  void initializeToRandom();

  bool cloneWritten(const ObjectState *src);
  void resetBytesWritten();
  bool isWritten() const { return writtenMask != nullptr; }
  unsigned getPhysicalSize() const { return object->size; }
  unsigned getVisibleSize() const { return object->size; }

  ref<Expr> read(ref<Expr> offset, Expr::Width width) const;
  ref<Expr> read(unsigned offset, Expr::Width width) const;
  ref<Expr> read8(unsigned offset) const;

  // return bytes written.
  void write(unsigned offset, ref<Expr> value);
  void write(ref<Expr> offset, ref<Expr> value);

  void write8(unsigned offset, uint8_t value);
  void write16(unsigned offset, uint16_t value);
  void write32(unsigned offset, uint32_t value);
  void write64(unsigned offset, uint64_t value);

  ref<Expr> read8(ref<Expr> offset) const;
  void write8(unsigned offset, ref<Expr> value);
  void write8(ref<Expr> offset, ref<Expr> value);

#ifdef NEVER
  /// state versions of allocation expressions
  ref<ConstantExpr> getBaseExpr() const {
    return ConstantExpr::create(object->address, Context::get().getPointerWidth());
  }
  ref<ConstantExpr> getSizeExpr() const {
    return ConstantExpr::create(visible_size, Context::get().getPointerWidth());
  }
  ref<Expr> getOffsetExpr(ref<Expr> pointer) const {
    return SubExpr::create(pointer, getBaseExpr());
  }
  ref<Expr> getBoundsCheckPointer(ref<Expr> pointer) const {
    return getBoundsCheckOffset(getOffsetExpr(pointer));
  }
  ref<Expr> getBoundsCheckPointer(ref<Expr> pointer, unsigned bytes) const {
    return getBoundsCheckOffset(getOffsetExpr(pointer), bytes);
  }

  ref<Expr> getBoundsCheckOffset(ref<Expr> offset) const {
    if (visible_size==0) {
      return EqExpr::create(offset,
                            ConstantExpr::alloc(0, Context::get().getPointerWidth()));
    } else {
      return UltExpr::create(offset, getSizeExpr());
    }
  }
  ref<Expr> getBoundsCheckOffset(ref<Expr> offset, unsigned bytes) const {
    if (bytes<=visible_size) {
      return UltExpr::create(offset,
                             ConstantExpr::alloc(visible_size - bytes + 1,
                                                 Context::get().getPointerWidth()));
    } else {
      return ConstantExpr::alloc(0, Expr::Bool);
    }
  }
#endif

private:
  const UpdateList &getUpdates() const;

  void makeConcrete();

  void makeSymbolic();


  void fastRangeCheckOffset(ref<Expr> offset, unsigned *base_r, 
                            unsigned *size_r) const;
  void flushRangeForRead(unsigned rangeBase, unsigned rangeSize) const;
  void flushRangeForWrite(unsigned rangeBase, unsigned rangeSize);

  bool isByteConcrete(unsigned offset) const;
  bool isByteFlushed(unsigned offset) const;
  bool isByteKnownSymbolic(unsigned offset) const;

  void markByteConcrete(unsigned offset);
  void markByteSymbolic(unsigned offset);
  void markByteFlushed(unsigned offset);
  void markByteUnflushed(unsigned offset);
  void setKnownSymbolic(unsigned offset, Expr *value);

  void print();
  ArrayCache *getArrayCache() const;
  
  bool isByteWritten(unsigned offset) const;
  void markByteWritten(unsigned offset);
};
  
} // End klee namespace

#endif
