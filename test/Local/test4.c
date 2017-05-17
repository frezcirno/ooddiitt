
#include <stdio.h>
#include <stdlib.h>
#include <klee/klee.h>
#include "mark.h"
/*  -*- Last-Edit:  Mon Dec  7 10:31:51 1992 by Tarak S. Goradia; -*- */

typedef char bool;
#define false 0
#define true 1

#define MAXSTR 100
#define MAXPAT MAXSTR

#define ENDSTR '\0'
#define ESCAPE '@'
#define CLOSURE '*'
#define BOL '%'
#define EOL '$'
#define ANY '?'
#define CCL '['
#define CCLEND ']'
#define NEGATE '^'
#define NCCL '!'
#define LITCHAR 'c'
#define DITTO -1
#define DASH '-'

#define TAB 9
#define NEWLINE 10

#define CLOSIZE 1

typedef char character;
typedef char string[MAXSTR];

int patsize(usher_t *usher, char *pat, int n) {
  return 0;
}

bool omatch(usher_t *usher, char *lin, int *i, char *pat, int j) {

  return false;
}

int drv(usher_t *usher, char *lin, int offset, char *pat, int j) {
  MARK(16, 23);
  int i, k;
  bool result, done;

  done = false;
  while (guide(usher, (MARK(16, 22), !done)) && guide(usher, (mark(16, 21), pat[j] != ENDSTR)))
    if (guide(usher, (mark(16, 20), pat[j] == CLOSURE))) {
      j = j + (mark(16, 19), patsize(NULL, pat, j));
      i = offset;
      while (guide(usher, (MARK(16, 18), !done)) && guide(usher, (mark(16, 17), lin[i] != ENDSTR))) {
        result = (mark(16, 16), omatch(NULL, lin, &i, pat, j));
        if (guide(usher, !result)) {
          (mark(16, 15), done = true);
        }
      }
      (mark(16, 13), done = false);
      while (guide(usher, (MARK(16, 12), !done)) && guide(usher, (mark(16, 11), i >= offset))) {
        k = drv(NULL, lin, i, pat, j + (mark(16, 10), patsize(NULL, pat, j)));
        if (guide(usher, k >= 0)) {
          (mark(16, 9), done = true);
        } else {
          (mark(16, 8), i = i - 1);
        }
      }
      (mark(16, 6), offset = k);
      done = true;
    } else {
      result = (mark(16, 5), omatch(NULL, lin, &offset, pat, j));
      if (guide(usher, !result)) {
        (mark(16, 4), offset = -1);
        done = true;
      } else {
        j = j + (mark(16, 3), patsize(NULL, pat, j));
      }
    }

  return (MARK(16, 1), offset);
}

//int drv(char *lin, int offset, char *pat, int j) {

//  return foo(NULL, lin, offset, pat, j);
//}

int main(int argc, char *argv[]) {

  char lin[3];
  int offset;
  char pat[3];
  int j;

  klee_make_symbolic(lin, sizeof(lin), "lin");
  klee_make_symbolic(&offset, sizeof(offset), "offset");
  klee_make_symbolic(pat, sizeof(pat), "pat");
  klee_make_symbolic(&j, sizeof(j), "j");
  klee_assume(offset >= 0);
  klee_assume(offset < 3);
  klee_assume(j >= 0);
  klee_assume(j < 3);

  drv(NULL, lin, offset, pat, j);
  return 0;
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

