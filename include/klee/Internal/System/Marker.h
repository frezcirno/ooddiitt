//
// Created by Richard Rutledge on 7 Feb 18.
//

#ifndef KLEE_MARKER_H
#define KLEE_MARKER_H

#include <sstream>

inline unsigned toMarker(unsigned fnID, unsigned mkID) { return (fnID * 1000) + mkID; }
inline unsigned getFNID(unsigned marker)               { return marker / 1000; }
inline unsigned getMKID(unsigned marker)               { return marker % 1000; }

class Marker {

public:

  char type;
  unsigned fn;
  unsigned id;

  Marker(char _type = 0, unsigned _fn = 0, unsigned _id = 0) :
      type(_type), fn(_fn), id(_id) {}

  // construction and assignment
  Marker(const Marker &m)    { copy(m); }
  inline Marker &operator=(const Marker &m)   { copy(m); return *this; }
  std::string to_string() const
    { std::stringstream ss; ss << type << ':' << fn << ':' << id; return ss.str(); }

private:
  void copy(const Marker &m) { type = m.type; fn = m.fn; id = m.id; }
};

// fundamental relations
inline bool operator==(const Marker &m1, const Marker &m2)
    { return m1.type == m2.type && m1.fn == m2.fn && m1.id == m2.id; }
inline bool operator<(const Marker &m1, const Marker &m2)
    { return (m1.type < m2.type) ||
             (m1.type == m2.type && m1.fn < m2.fn) ||
             (m1.type == m2.type && m1.fn == m2.fn && m1.id < m2.id); }

// derived relations
inline bool operator!=(const Marker &m1, const Marker &m2) { return !(m1 == m2); }
inline bool operator>(const Marker &m1, const Marker &m2)  { return m2 < m1; }
inline bool operator<=(const Marker &m1, const Marker &m2) { return !(m2 < m1); }
inline bool operator>=(const Marker &m1, const Marker &m2) { return !(m1 < m2); }

class MarkerSequence : public std::vector<Marker> {

public:
  void to_trace(klee::m2m_path_t &path) const {
    path.clear();
    for (auto itr = this->cbegin(), end = this->cend(); itr != end; ++itr) {
      if (toupper(itr->type) == 'M') {
        path.push_back(toMarker(itr->fn, itr->id));
      }
    }
  }

  void to_intra_traces(std::map<unsigned,klee::m2m_path_t> &map) const {
    map.clear();

    for (auto itr = this->cbegin(), end = this->cend(); itr != end; ++itr) {
      if (toupper(itr->type) == 'M') {
        map[itr->fn].push_back(toMarker(itr->fn, itr->id));
      }
    }
  }

  unsigned get_terminating_id() const {
    for (auto itr = this->crbegin(), end = this->crend(); itr != end; ++itr) {
      if (toupper(itr->type) == 'M') {
        return itr->id;
      }
    }
    return 0;
  };
};

#endif //KLEE_MARKER_H
