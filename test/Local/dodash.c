#include "mark.h"
/*  -*- Last-Edit:  Mon Dec  7 10:31:51 1992 by Tarak S. Goradia; -*- */

void Caseerror();
void change();
void subline();

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

int isalnum(int c) {
  return 0;
}


int addstr(char c, char *outset, int *j, int maxset) {
  MARK(2, 4);
  bool result;
  return (MARK(2, 1), result);
}

char esc(char *s, int *i) {
  MARK(3, 10);
  char result;
  return (MARK(3, 1), result);
}

void dodash(char delim, char *src, int *i, char *dest, int *j, int maxset) {
  MARK(4, 22);
  int k;
  bool junk;
  char escjunk;

  while (((MARK(4, 21), src[*i] != delim)) &&
         ((mark(4, 20), src[*i] != ENDSTR))) {
    if ((mark(4, 19), src[*i - 1] == ESCAPE)) {
      escjunk = (mark(4, 18), esc(src, i));
      junk = addstr(escjunk, dest, j, maxset);
    } else if ((mark(4, 17), src[*i] != DASH)) {
      junk = (mark(4, 16), addstr(src[*i], dest, j, maxset));
    } else if ((mark(4, 15), *j <= 1) || (mark(4, 14), src[*i + 1] == ENDSTR)) {
      junk = (mark(4, 13), addstr(DASH, dest, j, maxset));
    } else if (((mark(4, 12), isalnum(src[*i - 1]))) &&
               ((mark(4, 11), isalnum(src[*i + 1]))) &&
               ((mark(4, 10), src[*i - 1] <= src[*i + 1]))) {
      for ((mark(4, 9), k = src[*i - 1] + 1); (MARK(4, 8), k <= src[*i + 1]);
           (mark(4, 6), k++)) {
        junk = (mark(4, 7), addstr(k, dest, j, maxset));
      }
      (mark(4, 5), *i = *i + 1);
    } else {
      junk = (mark(4, 4), addstr(DASH, dest, j, maxset));
    }
    (mark(4, 3), (*i) = (*i) + 1);
  }
  MARK(4, 1);
  return;
}

