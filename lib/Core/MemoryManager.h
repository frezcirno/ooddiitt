//===-- MemoryManager.h -----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_MEMORYMANAGER_H
#define KLEE_MEMORYMANAGER_H

#include <set>
#include <stdint.h>

#include "klee/Internal/System/Memory.h"

namespace llvm {
class Value;
}

namespace klee {
class MemoryObject;
class ArrayCache;

class MemoryManager {
private:
  typedef std::set<MemoryObject *> objects_ty;
  objects_ty objects;
  ArrayCache *const arrayCache;

  char *deterministicSpace;
  char *nextFreeSlot;
  size_t spaceSize;
  uint64_t base_addr;

public:
  MemoryManager(ArrayCache *arrayCache);
  ~MemoryManager();

  void setBaseAddr(void *addr) { base_addr = (uint64_t) addr; }

  /**
   * Returns memory object which contains a handle to real virtual process
   * memory.
   */
  MemoryObject *allocate(uint64_t size, const llvm::Type *type, MemKind kind, const llvm::Value *allocSite, size_t alignment);
  MemoryObject *allocateFixed(uint64_t address, uint64_t size, const llvm::Value *allocSite);
  void markFreed(MemoryObject *mo);
  ArrayCache *getArrayCache() const { return arrayCache; }
  void dump() const;

  /*
   * Returns the size used by deterministic allocation in bytes
   */
  size_t getUsedDeterministicSize();
};

} // End klee namespace

#endif
