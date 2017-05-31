
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

int addstr(char c, char *outset, int *j, int maxset);
bool getccl(char *arg, int *i, char *pat, int *j);
bool in_set_2(char c);
void stclose(char *pat, int *j, int lastj);
char esc(char *s, int *i);
int amatch(char *lin, int offset, char *pat, int j);
void putsub(char *lin, int s1, int s2, char *sub);

// #ifdef NEVER
int makepat(char *arg, int start, char delim, char *pat) {
  MARK(9, 30);

  usher_t usher;
  constructUsher(&usher, 4);
  setBit(&usher, 0);
  setBit(&usher, 1);
  setBit(&usher, 2);
  setBit(&usher, 3);

  int result;

  int i, j, lastj, lj;
  bool done, junk;
  bool getres;
  char escjunk;

  j = 0;
  i = start;
  lastj = 0;
  done = false;
  while (((MARK(9, 29), guide(&usher, !done))) && ((mark(9, 28), guide(&usher, arg[i] != delim))) &&
         ((mark(9, 27), guide(&usher, arg[i] != ENDSTR)))) {
    (mark(9, 26), lj = j);
    if (guide(&usher, arg[i] == ANY)) {
      junk = (mark(9, 25), addstr(ANY, pat, &j, MAXPAT));
    } else if (((mark(9, 24), guide(&usher, arg[i] == BOL))) && ((mark(9, 23), guide(&usher, i == start)))) {
      junk = (mark(9, 22), addstr(BOL, pat, &j, MAXPAT));
    } else if (((mark(9, 21), guide(&usher, arg[i] == EOL))) &&
               ((mark(9, 20), guide(&usher, arg[i + 1] == delim)))) {
      junk = (mark(9, 19), addstr(EOL, pat, &j, MAXPAT));
    } else if ((mark(9, 18), guide(&usher, arg[i] == CCL))) {
      getres = (mark(9, 17), getccl(arg, &i, pat, &j));
      done = (bool)(getres == false);
    } else if (((mark(9, 16), guide(&usher, arg[i] == CLOSURE))) &&
               ((mark(9, 15), guide(&usher, i > start)))) {
      (mark(9, 14), lj = lastj);
      if (guide(&usher, in_set_2(pat[lj]))) {
        (mark(9, 13), done = true);
      } else {
        (mark(9, 12), stclose(pat, &j, lastj));
      }
    } else {
      junk = (mark(9, 11), addstr(LITCHAR, pat, &j, MAXPAT));
      escjunk = esc(arg, &i);
      junk = addstr(escjunk, pat, &j, MAXPAT);
    }
    (mark(9, 10), lastj = lj);
    if ((guide(&usher, !done))) {
      (mark(9, 9), i = i + 1);
    }
  }
  junk = (mark(9, 7), addstr(ENDSTR, pat, &j, MAXPAT));
  if ((guide(&usher, done)) || ((mark(9, 6), guide(&usher, arg[i] != delim)))) {
    (mark(9, 5), result = 0);
  } else if (((mark(9, 4), guide(&usher, !junk)))) {
    (mark(9, 3), result = 0);
  } else {
    (mark(9, 2), result = i);
  }

  return (MARK(9, 1), result);
}

//#endif

 #ifdef NEVER

int makesub(char *arg, int from, character delim, char *sub) {
  MARK(11, 14);

  usher_t usher;
  constructUsher(&usher, 1);
  setBit(&usher, 0);

  int result;
  int i, j;
  bool junk;
  character escjunk;

  j = 0;
  i = from;
  while (((MARK(11, 13), guide(&usher, arg[i] != delim))) &&
         ((mark(11, 12), guide(&usher, arg[i] != ENDSTR)))) {
    if ((mark(11, 11), guide(&usher, arg[i] == (unsigned)('&')))) {
      junk = (mark(11, 10), addstr(DITTO, sub, &j, MAXPAT));
    } else {
      escjunk = (mark(11, 9), esc(arg, &i));
      junk = addstr(escjunk, sub, &j, MAXPAT);
    }
    (mark(11, 8), i = i + 1);
  }
  if ((mark(11, 6), guide(&usher, arg[i] != delim))) {
    (mark(11, 5), result = 0);
  } else {
    junk = (mark(11, 4), addstr(ENDSTR, &(*sub), &j, MAXPAT));
    if ((guide(&usher, !junk))) {
      (mark(11, 3), result = 0);
    } else {
      (mark(11, 2), result = i);
    }
  }
  return (MARK(11, 1), result);
}

#endif

#ifdef NEVER

void subline(char *lin, char *pat, char *sub) {
  MARK(18, 11);

  usher_t usher;
  constructUsher(&usher, 3);
  setBit(&usher, 0);
  setBit(&usher, 1);
  setBit(&usher, 2);

  int i, lastm, m;

  lastm = -1;
  i = 0;
  while (((MARK(18, 10), guide(&usher, lin[i] != ENDSTR)))) {
    m = (mark(18, 9), amatch(lin, i, pat, 0));
    if ((guide(&usher, m >= 0)) && ((mark(18, 8), guide(&usher, lastm != m)))) {
      (mark(18, 7), putsub(lin, i, m, sub));
      lastm = m;
    }
    if (((mark(18, 6), guide(&usher, m == -1))) || ((mark(18, 5), guide(&usher, m == i)))) {
      (mark(18, 4), fputc(lin[i], stdout));
      i = i + 1;
    } else {
      (mark(18, 3), i = m);
    }
  }
  MARK(18, 1);
  return;
}

#endif