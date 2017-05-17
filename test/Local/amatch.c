#include "mark.h"
/*  -*- Last-Edit:  Mon Dec  7 10:31:51 1992 by Tarak S. Goradia; -*- */

typedef char bool;
#define false 0
#define true 1
#define NULL ((void*)0)
#define FILE void
#define stdout NULL
#define stdin  NULL

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

int patsize(char *pat, int n);
bool omatch(char *lin, int *i, char *pat, int j);
int foo(char *lin, int offset, char *pat, int j);

int drv(char *lin, int offset, char *pat, int j) {
  MARK(16, 23);
  int i, k;
  bool result, done;

  done = false;
  while (((MARK(16, 22), !done)) && ((mark(16, 21), pat[j] != ENDSTR)))
    if ((mark(16, 20), pat[j] == CLOSURE)) {
      j = j + (mark(16, 19), patsize(pat, j));
      i = offset;
      while (((MARK(16, 18), !done)) && ((mark(16, 17), lin[i] != ENDSTR))) {
        result = (mark(16, 16), omatch(lin, &i, pat, j));
        if (!result) {
          (mark(16, 15), done = true);
        }
      }
      (mark(16, 13), done = false);
      while (((MARK(16, 12), !done)) && ((mark(16, 11), i >= offset))) {
        k = foo(lin, i, pat, j + (mark(16, 10), patsize(pat, j)));
        if ((k >= 0)) {
          (mark(16, 9), done = true);
        } else {
          (mark(16, 8), i = i - 1);
        }
      }
      (mark(16, 6), offset = k);
      done = true;
    } else {
      result = (mark(16, 5), omatch(lin, &offset, pat, j));
      if ((!result)) {
        (mark(16, 4), offset = -1);
        done = true;
      } else {
        j = j + (mark(16, 3), patsize(pat, j));
      }
    }

  return (MARK(16, 1), offset);
}

