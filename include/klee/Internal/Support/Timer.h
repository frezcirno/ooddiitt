//===-- Timer.h -------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_TIMER_H
#define KLEE_TIMER_H

#include <stdint.h>
#include <chrono>
#include <map>
#include <vector>

namespace klee {
  class WallTimer {
    uint64_t startMicroseconds;
    
  public:
    WallTimer();

    /// check - Return the delta since the timer was created, in microseconds.
    uint64_t check();
  };
  class MonotonicTimer {
  public:
    MonotonicTimer() { start_time = std::chrono::steady_clock::now(); }

    void set(unsigned id, unsigned secs) {
      if (id > 0) end_times[id] = start_time + std::chrono::seconds(secs);
    }

    void clear(unsigned id) {
      if (id > 0) {
        auto itr = end_times.find(id);
        if (itr != end_times.end()) end_times.erase(itr);
      }
    }

    unsigned expired() {
      start_time = std::chrono::steady_clock::now();
      for (const auto &pr : end_times) {
        if (pr.second < start_time) {
          return pr.first;
        }
      }
      return 0;
    }

  private:
    std::chrono::time_point<std::chrono::steady_clock> start_time;
    std::map<unsigned,std::chrono::time_point<std::chrono::steady_clock> >end_times;
  };
}

#endif

