#ifndef MARK_INCLUDED
#define MARK_INCLUDED

void mark(unsigned fn, unsigned bb);
void MARK(unsigned fn, unsigned bb);

typedef struct {
  unsigned size;
  unsigned next;
  unsigned *bits;
} usher_t;

void constructUsher(usher_t *usher, unsigned size);
void deleteUsher(usher_t *usher);
int guide(usher_t *usher, int arg);

unsigned getBit(const usher_t *usher, unsigned idx);
void setBit(usher_t *usher, unsigned idx);
void clearBit(usher_t *usher, unsigned idx);

#endif // MARK_INCLUDED

