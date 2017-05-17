#include <stdlib.h>
#include "mark.h"

void bar();

void foo(usher_t *usher, int flag) {

  if ((MARK(1, 5), guide(usher, flag))) {
    while ((MARK(1, 4), guide(usher, !flag))) {
      (mark(1, 3), bar());
    }
  }
  MARK(1, 1);
  return;
}

void drv(int flag) {
  foo(NULL, flag);
}

void mark(unsigned fn, unsigned bb) { }
void MARK(unsigned fn, unsigned bb) { }

void constructUsher(usher_t *usher, unsigned size) {
  usher->size = size;
  usher->next = 0;
  usher->bits = (unsigned *) malloc((size + 31) / 32);
}

void deleteUsher(usher_t *usher) {

  free(usher->bits);
#ifndef NDEBUG
  usher->size = 0;
  usher->next = 0;
  usher->bits = NULL;
#endif
}

unsigned getBit(const usher_t *usher, unsigned idx) {
  return ((usher->bits[idx/32]>>(idx&0x1F))&1);
}

void setBit(usher_t *usher, unsigned idx) {
  usher->bits[idx/32] |= 1<<(idx&0x1F);
}

void clearBit(usher_t *usher, unsigned idx) {
  usher->bits[idx/32] &= ~(1<<(idx&0x1F));
}

int guide(usher_t *usher, int arg) {

  int flag0 = 0;
  int flag1 = 1;

  if ((usher != NULL) && (usher->next < usher->size)) {
    flag0 = flag1 = getBit(usher, usher->next++);
  }
  return flag1 && (flag0 || arg);
}

