//===-- MemoryManager.cpp -------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "CoreStats.h"
#include "klee/Internal/System/Memory.h"
#include "MemoryManager.h"

#include "klee/Expr.h"
#include "klee/Internal/Support/ErrorHandling.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MathExtras.h"

#include <inttypes.h>
#include <sys/mman.h>

using namespace klee;

namespace {
llvm::cl::opt<bool> DeterministicAllocation(
    "allocate-determ",
    llvm::cl::desc("Allocate memory deterministically(default=off)"),
    llvm::cl::init(true));

llvm::cl::opt<bool>
    NullOnZeroMalloc("return-null-on-zero-malloc",
                     llvm::cl::desc("Returns NULL in case malloc(size) was "
                                    "called with size 0 (default=off)."),
                     llvm::cl::init(false));

llvm::cl::opt<unsigned> RedZoneSpace(
    "red-zone-space",
    llvm::cl::desc("Set the amount of free space between allocations. This is "
                   "important to detect out-of-bound accesses (default=10)."),
    llvm::cl::init(10));
}

/***/
MemoryManager::MemoryManager(ArrayCache *_arrayCache, void *user_base, size_t user_size)
    : arrayCache(_arrayCache), deterministicStart(nullptr), deterministicEnd(nullptr), nextFreeSlot(nullptr) {

  if (DeterministicAllocation) {
    if (user_base != nullptr) deterministicStart = (char*) user_base;
    else deterministicStart = (char*) 0x7ff30000000;
    nextFreeSlot = deterministicStart;
    if (user_size == 0) user_size = 1024 * 1024 * 1024;
    deterministicEnd = (void*) ((char*) deterministicStart + user_size);
  }
}

MemoryManager::~MemoryManager() {

  // deleting an mo automagically removes it from the memory manager
  // therefore, cannot iterate over the objects.  just delete them until objects is empty
//  while (!objects.empty()) {
//    const MemoryObject *mo = *objects.begin();
//    if (!DeterministicAllocation) {
//      free((void*) mo->address);
//    }
//    delete mo;
//  }
}

MemoryObject *MemoryManager::allocate(uint64_t size, const llvm::Type *type, MemKind kind, const llvm::Value *allocSite, size_t alignment) {
  if (size > 10 * 1024 * 1024)
    klee_warning_once(0, "Large alloc: %" PRIu64
                         " bytes.  KLEE may run out of memory.",
                      size);

  // Return NULL if size is zero, this is equal to error during allocation
  if (NullOnZeroMalloc && size == 0)
    return 0;

  if (!llvm::isPowerOf2_64(alignment)) {
    klee_warning("Only alignment of power of two is supported");
    return 0;
  }

  uint64_t address = 0;
  if (DeterministicAllocation) {

    address = llvm::RoundUpToAlignment((uint64_t) nextFreeSlot + alignment - 1, alignment);

    // Handle the case of 0-sized allocations as 1-byte allocations.
    // This way, we make sure we have this allocation between its own red zones
    size_t alloc_size = std::max(size, (uint64_t)1);
    if ((char *) address + alloc_size < deterministicEnd) {
      nextFreeSlot = (void*) ((char *) address + (alloc_size + RedZoneSpace));
    } else {
      klee_warning_once(0, "Couldn't allocate %" PRIu64
                           " bytes. Not enough deterministic space left.",
                        size);
      address = 0;
    }
  } else {
    // Use malloc for the standard case
    if (alignment <= 8)
      address = (uint64_t) malloc(size);
    else {
      int res = posix_memalign((void **)&address, alignment, size);
      if (res < 0) {
        klee_warning("Allocating aligned memory failed.");
        address = 0;
      }
    }
  }

  if (!address)
    return nullptr;

  if ((Context::get().getPointerWidth() == Expr::Int32) && (address > UINT32_MAX)) {
    klee_error("32-bit memory allocation requires 64 bit value");
  }

  ++stats::allocations;
  MemoryObject *res = new MemoryObject(address, size, alignment, type, kind, allocSite, this);
  res->count = 1;
  return res;
}

MemoryObject *MemoryManager::inject(void *addr, uint64_t size, const llvm::Type *type, MemKind kind, size_t alignment) {

  MemoryObject *result = nullptr;
  if (DeterministicAllocation) {

    // RLR TODO: should we insure this does not overlap an existing injection or allocation?
    result = new MemoryObject((uint64_t) addr, size, alignment, type, kind, nullptr, this);
  }
  return result;
}

void MemoryManager::markFreed(MemoryObject *mo) {
  if (!DeterministicAllocation)
    free((void *) (mo->address));
}

size_t MemoryManager::getUsedDeterministicSize() const {
  return ((char*) nextFreeSlot) - ((char*) deterministicStart);
}

size_t MemoryManager::getAvailable() const {
  return ((char*) deterministicEnd) - ((char*) nextFreeSlot);
}


void MemoryManager::dump() const {

//  llvm::outs() << objects.size() << "\n";
//
//  for (auto itr = objects.begin(), end = objects.end(); itr != end; ++itr ) {
//    auto obj = *itr;
//    llvm::outs() << obj->name << " " << (unsigned) obj->kind << "\n";
//  }
}
