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

void abort(void);
void exit(int exitlevel);
int addstr(char c, char *outset, int *j, int maxset);

void stclose(char *pat, int *j, int lastj) {
  MARK(6, 5);
  int jt;
  int jp;
  bool junk;

  for (jp = *j - 1; (MARK(6, 4), jp >= lastj); (mark(6, 2), jp--)) {
    (mark(6, 3), jt = jp + CLOSIZE);
    junk = addstr(pat[jp], pat, &jt, MAXPAT);
  }
  *j = *j + CLOSIZE;
  pat[lastj] = CLOSURE;
  MARK(6, 1);
  return;
}

int addstr(char c, char *outset, int *j, int maxset) {
  MARK(2, 4);
  bool result;
  return (MARK(2, 1), result);
}

