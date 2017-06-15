
/*  -*- Last-Edit:  Mon Dec  7 10:31:51 1992 by Tarak S. Goradia; -*- */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include "mark.h"

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

int patsize(char *pat, int n);
bool omatch(char *lin, int *i, char *pat, int j);

void test(char a1, short a2, int a3, long a4);

int amatch(char *lin, int offset, char *pat, int j) {
  MARK(16, 23);
  int i, k;
  bool result, done;

  char a1;
  short a2;
  int a3;
  long a4;

  test(a1, a2, a3, a4);

  done = false;
//  while (((MARK(16, 22), !done)) && ((mark(16, 21), pat[j] != ENDSTR)))
//    if ((mark(16, 20), pat[j] == CLOSURE)) {
      j = j + (mark(16, 19), patsize(pat, j));
      i = offset;
      while (((MARK(16, 18), !done)) && ((mark(16, 17), lin[i] != ENDSTR))) {
        result = (mark(16, 16), omatch(lin, &i, pat, j));
        if (!result) {
          (mark(16, 15), done = true);
        }
      }
//    } 
  return (MARK(16, 1), offset);
}

