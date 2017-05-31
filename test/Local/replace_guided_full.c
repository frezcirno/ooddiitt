
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

void Caseerror(usher_t *usher, int n) {
  (void)(MARK(21, 1), fprintf(stdout, "Missing case limb: line %d\n", n));
  (MARK(21, 13), exit(4));
}

bool my_getline(usher_t *usher, char *s, int maxsize) {
  MARK(1, 1);
  char *result;
  result = fgets(s, maxsize, stdin);
  bool result_dff36ebb57 = (s != NULL);
  return (MARK(1, 13), (result_dff36ebb57));
}

int addstr(usher_t *usher, char c, char *outset, int *j, int maxset) {
  MARK(2, 4);
  bool result;
  if (guide(usher, *j >= maxset)) {
    (mark(2, 3), result = false);
  } else {
    (mark(2, 2), outset[*j] = c);
    *j = *j + 1;
    result = true;
  }
  return (MARK(2, 1), result);
}

char esc(usher_t *usher, char *s, int *i) {
  MARK(3, 10);
  char result;
  if (guide(usher, s[*i] != ESCAPE)) {
    (mark(3, 9), result = s[*i]);
  } else if ((mark(3, 8), guide(usher, s[*i + 1] == ENDSTR))) {
    (mark(3, 7), result = ESCAPE);
  } else {
    (mark(3, 6), *i = *i + 1);
    if (guide(usher, s[*i] == 'n')) {
      (mark(3, 5), result = NEWLINE);
    } else if ((mark(3, 4), guide(usher, s[*i] == 't'))) {
      (mark(3, 3), result = TAB);
    } else {
      (mark(3, 2), result = s[*i]);
    }
  }
  return (MARK(3, 1), result);
}

void dodash(usher_t *usher, char delim, char *src, int *i, char *dest, int *j, int maxset) {
  MARK(4, 22);
  int k;
  bool junk;
  char escjunk;

  while (((MARK(4, 21), guide(usher, src[*i] != delim))) &&
         ((mark(4, 20), guide(usher, src[*i] != ENDSTR)))) {
    if ((mark(4, 19), guide(usher, src[*i - 1] == ESCAPE))) {
      escjunk = (mark(4, 18), esc(NULL, src, i));
      junk = addstr(NULL, escjunk, dest, j, maxset);
    } else if ((mark(4, 17), guide(usher, src[*i] != DASH))) {
      junk = (mark(4, 16), addstr(NULL, src[*i], dest, j, maxset));
    } else if ((mark(4, 15), guide(usher, *j <= 1)) || (mark(4, 14), guide(usher, src[*i + 1] == ENDSTR))) {
      junk = (mark(4, 13), addstr(NULL, DASH, dest, j, maxset));
    } else if (((mark(4, 12), guide(usher, isalnum(src[*i - 1])))) &&
               ((mark(4, 11), guide(usher, isalnum(src[*i + 1])))) &&
               ((mark(4, 10), guide(usher, src[*i - 1] <= src[*i + 1])))) {
      for ((mark(4, 9), k = src[*i - 1] + 1); (MARK(4, 8), guide(usher, k <= src[*i + 1]));
           (mark(4, 6), k++)) {
        junk = (mark(4, 7), addstr(NULL, k, dest, j, maxset));
      }
      (mark(4, 5), *i = *i + 1);
    } else {
      junk = (mark(4, 4), addstr(NULL, DASH, dest, j, maxset));
    }
    (mark(4, 3), (*i) = (*i) + 1);
  }
  MARK(4, 1);
  return;
}

bool getccl(usher_t *usher, char *arg, int *i, char *pat, int *j) {
  MARK(5, 4);
  int jstart;
  bool junk;

  *i = *i + 1;
  if (guide(usher, arg[*i] == NEGATE)) {
    junk = (mark(5, 3), addstr(NULL, NCCL, pat, j, MAXPAT));
    *i = *i + 1;
  } else {
    junk = (mark(5, 2), addstr(NULL, CCL, pat, j, MAXPAT));
  }
  jstart = *j;
  junk = addstr(NULL, 0, pat, j, MAXPAT);
  dodash(NULL, CCLEND, arg, i, pat, j, MAXPAT);
  pat[jstart] = *j - jstart - 1;
  bool result_082fd44040 = (arg[*i] == CCLEND);
  return (MARK(5, 1), (result_082fd44040));
}

void stclose(usher_t *usher, char *pat, int *j, int lastj) {
  MARK(6, 5);
  int jt;
  int jp;
  bool junk;

  for (jp = *j - 1; (MARK(6, 4), guide(usher, jp >= lastj)); (mark(6, 2), jp--)) {
    (mark(6, 3), jt = jp + CLOSIZE);
    junk = addstr(NULL, pat[jp], pat, &jt, MAXPAT);
  }
  *j = *j + CLOSIZE;
  pat[lastj] = CLOSURE;
  MARK(6, 1);
  return;
}

bool in_set_2(usher_t *usher, char c) {
  bool result_a0b4887c98 = ((MARK(7, 4), c == BOL) || (mark(7, 3), c == EOL) ||
                            (mark(7, 2), c == CLOSURE));
  return (MARK(7, 1), (result_a0b4887c98));
}

bool in_pat_set(usher_t *usher, char c) {
  bool result_3b3a0d7955 =
      ((MARK(8, 8), c == LITCHAR) || (mark(8, 7), c == BOL) ||
       (mark(8, 6), c == EOL) || (mark(8, 5), c == ANY) ||
       (mark(8, 4), c == CCL) || (mark(8, 3), c == NCCL) ||
       (mark(8, 2), c == CLOSURE));
  return (MARK(8, 1), (result_3b3a0d7955));
}

int makepat(usher_t *usher, char *arg, int start, char delim, char *pat) {
  MARK(9, 30);
  int result;

  int i, j, lastj, lj;
  bool done, junk;
  bool getres;
  char escjunk;

  j = 0;
  i = start;
  lastj = 0;
  done = false;
  while (((MARK(9, 29), guide(usher, !done))) && ((mark(9, 28), guide(usher, arg[i] != delim))) &&
         ((mark(9, 27), guide(usher, arg[i] != ENDSTR)))) {
    (mark(9, 26), lj = j);
    if (guide(usher, arg[i] == ANY)) {
      junk = (mark(9, 25), addstr(NULL, ANY, pat, &j, MAXPAT));
    } else if (((mark(9, 24), guide(usher, arg[i] == BOL))) && ((mark(9, 23), guide(usher, i == start)))) {
      junk = (mark(9, 22), addstr(NULL, BOL, pat, &j, MAXPAT));
    } else if (((mark(9, 21), guide(usher, arg[i] == EOL))) &&
               ((mark(9, 20), guide(usher, arg[i + 1] == delim)))) {
      junk = (mark(9, 19), addstr(NULL, EOL, pat, &j, MAXPAT));
    } else if ((mark(9, 18), guide(usher, arg[i] == CCL))) {
      getres = (mark(9, 17), getccl(NULL, arg, &i, pat, &j));
      done = (bool)(getres == false);
    } else if (((mark(9, 16), guide(usher, arg[i] == CLOSURE))) &&
               ((mark(9, 15), guide(usher, i > start)))) {
      (mark(9, 14), lj = lastj);
      if (guide(usher, in_set_2(NULL, pat[lj]))) {
        (mark(9, 13), done = true);
      } else {
        (mark(9, 12), stclose(NULL, pat, &j, lastj));
      }
    } else {
      junk = (mark(9, 11), addstr(NULL, LITCHAR, pat, &j, MAXPAT));
      escjunk = esc(NULL, arg, &i);
      junk = addstr(NULL, escjunk, pat, &j, MAXPAT);
    }
    (mark(9, 10), lastj = lj);
    if ((guide(usher, !done))) {
      (mark(9, 9), i = i + 1);
    }
  }
  junk = (mark(9, 7), addstr(NULL, ENDSTR, pat, &j, MAXPAT));
  if ((guide(usher, done)) || ((mark(9, 6), guide(usher, arg[i] != delim)))) {
    (mark(9, 5), result = 0);
  } else if (((mark(9, 4), guide(usher, !junk)))) {
    (mark(9, 3), result = 0);
  } else {
    (mark(9, 2), result = i);
  }

  return (MARK(9, 1), result);
}

int getpat(usher_t *usher, char *arg, char *pat) {
  MARK(10, 1);
  int makeres;

  makeres = makepat(NULL, arg, 0, ENDSTR, pat);
  int result_bc06c07c15 = (makeres > 0);
  return (MARK(10, 13), (result_bc06c07c15));
}

int makesub(usher_t *usher, char *arg, int from, character delim, char *sub) {
  MARK(11, 14);
  int result;
  int i, j;
  bool junk;
  character escjunk;

  j = 0;
  i = from;
  while (((MARK(11, 13), guide(usher, arg[i] != delim))) &&
         ((mark(11, 12), guide(usher, arg[i] != ENDSTR)))) {
    if ((mark(11, 11), guide(usher, arg[i] == (unsigned)('&')))) {
      junk = (mark(11, 10), addstr(NULL, DITTO, sub, &j, MAXPAT));
    } else {
      escjunk = (mark(11, 9), esc(NULL, arg, &i));
      junk = addstr(NULL, escjunk, sub, &j, MAXPAT);
    }
    (mark(11, 8), i = i + 1);
  }
  if ((mark(11, 6), guide(usher, arg[i] != delim))) {
    (mark(11, 5), result = 0);
  } else {
    junk = (mark(11, 4), addstr(NULL, ENDSTR, &(*sub), &j, MAXPAT));
    if ((guide(usher, !junk))) {
      (mark(11, 3), result = 0);
    } else {
      (mark(11, 2), result = i);
    }
  }
  return (MARK(11, 1), result);
}

bool getsub(usher_t *usher, char *arg, char *sub) {
  MARK(12, 1);
  int makeres;

  makeres = makesub(NULL, arg, 0, ENDSTR, sub);
  bool result_61a37a6fe9 = (makeres > 0);
  return (MARK(12, 13), (result_61a37a6fe9));
}

bool locate(usher_t *usher, character c, char *pat, int offset) {
  MARK(13, 7);
  int i;
  bool flag;

  flag = false;
  i = offset + pat[offset];
  while (((MARK(13, 6), guide(usher, i > offset)))) {
    if ((mark(13, 5), guide(usher, c == pat[i]))) {
      (mark(13, 4), flag = true);
      i = offset;
    } else {
      (mark(13, 3), i = i - 1);
    }
  }
  return (MARK(13, 1), flag);
}

bool omatch(usher_t *usher, char *lin, int *i, char *pat, int j) {
  MARK(14, 29);
  char advance;
  bool result;

  advance = -1;
  if (guide(usher, lin[*i] == ENDSTR)) {
    (mark(14, 28), result = false);
  } else {
    if (!(mark(14, 27), guide(usher, in_pat_set(NULL, pat[j])))) {
      (void) fprintf(stdout, "in omatch: can't happen\n");
      (MARK(14, 26), abort());
    } else {
      switch ((mark(14, 5), pat[j])) {
      case LITCHAR:
        if ((mark(14, 25), guide(usher, lin[*i] == pat[j + 1]))) {
          (mark(14, 24), advance = 1);
        }
        break;
      case BOL:
        if ((mark(14, 22), guide(usher, *i == 0))) {
          (mark(14, 21), advance = 0);
        }
        break;
      case ANY:
        if ((mark(14, 19), guide(usher, lin[*i] != NEWLINE))) {
          (mark(14, 18), advance = 1);
        }
        break;
      case EOL:
        if ((mark(14, 16), guide(usher, lin[*i] == NEWLINE))) {
          (mark(14, 15), advance = 0);
        }
        break;
      case CCL:
        if ((mark(14, 13), guide(usher, locate(NULL, lin[*i], pat, j + 1)))) {
          (mark(14, 12), advance = 1);
        }
        break;
      case NCCL:
        if (((mark(14, 10), guide(usher, lin[*i] != NEWLINE))) &&
            (!(mark(14, 9), guide(usher, locate(NULL, lin[*i], pat, j + 1))))) {
          (mark(14, 8), advance = 1);
        }
        break;
      default:
        (mark(14, 6), Caseerror(NULL, pat[j]));
      };
    }
  }
  if (((MARK(14, 4), guide(usher, advance >= 0)))) {
    (mark(14, 3), *i = *i + advance);
    result = true;
  } else {
    (mark(14, 2), result = false);
  }
  return (MARK(14, 1), result);
}

int patsize(usher_t *usher, char *pat, int n) {
  MARK(15, 12);
  int size;
  if (guide(usher, !in_pat_set(NULL, pat[n]))) {
    (void) fprintf(stdout, "in patsize: can't happen\n");
    (MARK(15, 11), abort());
  } else
    switch ((mark(15, 2), pat[n])) {
    case LITCHAR:
      (mark(15, 10), size = 2);
      break;

    case BOL:
    case EOL:
    case ANY:
      (mark(15, 7), size = 1);
      break;
    case CCL:
    case NCCL:
      (mark(15, 5), size = pat[n + 1] + 2);
      break;
    case CLOSURE:
      (mark(15, 4), size = CLOSIZE);
      break;
    default:
      (mark(15, 3), Caseerror(NULL, pat[n]));
    }
  return (MARK(15, 1), size);
}

int amatch(usher_t *usher, char *lin, int offset, char *pat, int j) {
  MARK(16, 23);
  int i, k;
  bool result, done;

  done = false;
  while (((MARK(16, 22), guide(usher, !done))) && ((mark(16, 21), guide(usher, pat[j] != ENDSTR))))
    if ((mark(16, 20), guide(usher, pat[j] == CLOSURE))) {
      j = j + (mark(16, 19), patsize(NULL, pat, j));
      i = offset;
      while (((MARK(16, 18), guide(usher, !done))) && ((mark(16, 17), guide(usher, lin[i] != ENDSTR)))) {
        result = (mark(16, 16), omatch(NULL, lin, &i, pat, j));
        if (guide(usher, !result)) {
          (mark(16, 15), done = true);
        }
      }
      (mark(16, 13), done = false);
      while (((MARK(16, 12), guide(usher, !done))) && ((mark(16, 11), guide(usher, i >= offset)))) {
        k = amatch(NULL, lin, i, pat, j + (mark(16, 10), patsize(NULL, pat, j)));
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

void putsub(usher_t *usher, char *lin, int s1, int s2, char *sub) {
  MARK(17, 11);
  int i;
  int j;

  i = 0;
  while (((MARK(17, 10), guide(usher, sub[i] != ENDSTR)))) {
    if ((mark(17, 9), guide(usher, sub[i] == DITTO)))
      for ((mark(17, 8), j = s1); (MARK(17, 7), guide(usher, j < s2)); (mark(17, 5), j++)) {
        (mark(17, 6), fputc(lin[j], stdout));
      }
    else {
      (mark(17, 4), fputc(sub[i], stdout));
    }
    (mark(17, 3), i = i + 1);
  }
  MARK(17, 1);
  return;
}

void subline(usher_t *usher, char *lin, char *pat, char *sub) {
  MARK(18, 11);
  int i, lastm, m;

  lastm = -1;
  i = 0;
  while (((MARK(18, 10), guide(usher, lin[i] != ENDSTR)))) {
    m = (mark(18, 9), amatch(NULL, lin, i, pat, 0));
    if ((guide(usher, m >= 0)) && ((mark(18, 8), guide(usher, lastm != m)))) {
      (mark(18, 7), putsub(NULL, lin, i, m, sub));
      lastm = m;
    }
    if (((mark(18, 6), guide(usher, m == -1))) || ((mark(18, 5), guide(usher, m == i)))) {
      (mark(18, 4), fputc(lin[i], stdout));
      i = i + 1;
    } else {
      (mark(18, 3), i = m);
    }
  }
  MARK(18, 1);
  return;
}

void change(usher_t *usher, char *pat, char *sub) {
  MARK(19, 5);
  string line;
  bool result;

  result = my_getline(NULL, line, MAXSTR);
  while ((MARK(19, 4), (guide(usher, result)))) {
    (mark(19, 3), subline(NULL, line, pat, sub));
    result = my_getline(NULL, line, MAXSTR);
  }
  MARK(19, 1);
  return;
}

#ifdef NEVER

int main(int argc, char *argv[]) {
  MARK(20, 9);
  string pat, sub;
  bool result;

  if (argc < 2) {
    (void) fprintf(stdout, "usage: change from [to]\n");
    (MARK(20, 8), exit(1));
  };

  result = (MARK(20, 7), getpat(argv[1], pat));
  if (!result) {
    (void) fprintf(stdout, "change: illegal \"from\" pattern\n");
    (MARK(20, 6), exit(2));
  }

  if ((MARK(20, 5), argc >= 3)) {
    result = (mark(20, 4), getsub(argv[2], sub));
    if (!result) {
      (void) fprintf(stdout, "change: illegal \"to\" string\n");
      (MARK(20, 3), exit(3));
    }
  } else {
    (mark(20, 2), sub[0] = '\0');
  }

  change(pat, sub);
  return (MARK(20, 1), 0);
}

#endif

