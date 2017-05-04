
/*  -*- Last-Edit:  Mon Dec  7 10:31:51 1992 by Tarak S. Goradia; -*- */
#include "mark.h"


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

typedef char string[MAXSTR];

void abort(void);
void exit(int exitlevel);
char *fgets(char *str, int count, FILE *stream);
int zop_fprintf1(FILE *stream, const char *format);
int zop_fprintf2(FILE *stream, const char *format, int n);
int fputc(int character, FILE *stream);
int isalnum(int c);

void Caseerror(int n);

int my_getline(char *s, int maxsize) {
  MARK(1, 1);
  char *result;
  int flag;

  result = fgets(s, maxsize, stdin);
  flag = ((result != NULL));
  MARK(1, 2);
  return flag;
}

int addstr(char c, char *outset, int *j, int maxset) {
  MARK(2, 1);
  int result;
  if (*j >= maxset)
    (mark(2, 2), result = false);
  else {
    (mark(2, 3), outset[*j] = c);
    *j = *j + 1;
    result = true;
  }
  MARK(2, 4);
  return result;
}

char esc(char *s, int *i) {
  MARK(3, 1);
  char result;
  if (s[*i] != ESCAPE)
    (mark(3, 2), result = s[*i]);
  else if ((mark(3, 3), s[*i + 1] == ENDSTR))
    (mark(3, 4), result = ESCAPE);
  else {
    (mark(3, 5), *i = *i + 1);
    if (s[*i] == 'n')
      (mark(3, 6), result = NEWLINE);
    else if ((mark(3, 7), s[*i] == 't'))
      (mark(3, 8), result = TAB);
    else
      (mark(3, 9), result = s[*i]);
  }
  MARK(3, 10);
  return result;
}

void dodash(char delim, char *src, int *i, char *dest, int *j, int maxset) {
  MARK(4, 1);
  int k;
  int junk;
  char escjunk;

  while (((MARK(4, 2), src[*i] != delim)) &&
         ((mark(4, 3), src[*i] != ENDSTR))) {
    if ((mark(4, 4), src[*i - 1] == ESCAPE)) {
      escjunk = (mark(4, 5), esc(src, i));
      junk = addstr(escjunk, dest, j, maxset);
    } else if ((mark(4, 6), src[*i] != DASH))
      junk = (mark(4, 7), addstr(src[*i], dest, j, maxset));
    else if ((mark(4, 8), *j <= 1) || (mark(4, 9), src[*i + 1] == ENDSTR))
      junk = (mark(4, 10), addstr(DASH, dest, j, maxset));
    else if (((mark(4, 11), isalnum(src[*i - 1]))) &&
             ((mark(4, 12), isalnum(src[*i + 1]))) &&
             ((mark(4, 13), src[*i - 1] <= src[*i + 1]))) {
      for ((mark(4, 14), k = src[*i - 1] + 1); (MARK(4, 15), k <= src[*i + 1]);
           (mark(4, 17), k++)) {
        junk = (mark(4, 16), addstr(k, dest, j, maxset));
      }
      (mark(4, 18), *i = *i + 1);
    } else
      junk = (mark(4, 19), addstr(DASH, dest, j, maxset));
    (mark(4, 20), (*i) = (*i) + 1);
  }
  MARK(4, 21);
}

int getccl(char *arg, int *i, char *pat, int *j) {
  MARK(5, 1);
  int jstart;
  int junk;
  int result;

  *i = *i + 1;
  if (arg[*i] == NEGATE) {
    junk = (mark(5, 2), addstr(NCCL, pat, j, MAXPAT));
    *i = *i + 1;
  } else
    junk = (mark(5, 3), addstr(CCL, pat, j, MAXPAT));
  (mark(5, 4), jstart = *j);
  junk = addstr(0, pat, j, MAXPAT);
  dodash(CCLEND, arg, i, pat, j, MAXPAT);
  pat[jstart] = *j - jstart - 1;
  result = (arg[*i] == CCLEND);
  MARK(5, 5);
  return result;
}

void stclose(char *pat, int *j, int lastj) {
  MARK(6, 1);
  int jt;
  int jp;
  int junk;

  for (jp = *j - 1; (MARK(6, 2), jp >= lastj); (mark(6, 4), jp--)) {
    (mark(6, 3), jt = jp + CLOSIZE);
    junk = addstr(pat[jp], pat, &jt, MAXPAT);
  }
  (mark(6, 5), *j = *j + CLOSIZE);
  pat[lastj] = CLOSURE;
  MARK(6, 6);
}

int in_set_2(char c) {
  MARK(7, 1);
  int result;
  result = ((mark(7, 4),
             c == BOL || (mark(7, 2), c == EOL) || (mark(7, 3), c == CLOSURE)));
  MARK(7, 5);
  return result;
}

int in_pat_set(char c) {
  MARK(8, 1);
  int result;
  result = ((mark(8, 8),
             c == LITCHAR || (mark(8, 2), c == BOL) || (mark(8, 3), c == EOL) ||
                 (mark(8, 4), c == ANY) || (mark(8, 5), c == CCL) ||
                 (mark(8, 6), c == NCCL) || (mark(8, 7), c == CLOSURE)));
  MARK(8, 9);
  return result;
}

int makepat(char *arg, int start, char delim, char *pat) {
  MARK(9, 1);
  int result;
  int i;
  int j;
  int lastj;
  int lj;
  int done, junk;
  int getres;
  char escjunk;

  j = 0;
  i = start;
  lastj = 0;
  done = false;
  while (((MARK(9, 2), !done)) && ((mark(9, 3), arg[i] != delim)) &&
         ((mark(9, 4), arg[i] != ENDSTR))) {
    (mark(9, 5), lj = j);
    if (arg[i] == ANY)
      junk = (mark(9, 6), addstr(ANY, pat, &j, MAXPAT));
    else if (((mark(9, 7), arg[i] == BOL)) && ((mark(9, 8), i == start)))
      junk = (mark(9, 9), addstr(BOL, pat, &j, MAXPAT));
    else if (((mark(9, 10), arg[i] == EOL)) &&
             ((mark(9, 11), arg[i + 1] == delim)))
      junk = (mark(9, 12), addstr(EOL, pat, &j, MAXPAT));
    else if ((mark(9, 13), arg[i] == CCL)) {
      getres = (mark(9, 14), getccl(arg, &i, pat, &j));
      done = (int)(getres == false);
    } else if (((mark(9, 15), arg[i] == CLOSURE)) &&
               ((mark(9, 16), i > start))) {
      (mark(9, 17), lj = lastj);
      if (in_set_2(pat[lj]))
        (mark(9, 18), done = true);
      else
        (mark(9, 19), stclose(pat, &j, lastj));
    } else {
      junk = (mark(9, 20), addstr(LITCHAR, pat, &j, MAXPAT));
      escjunk = esc(arg, &i);
      junk = addstr(escjunk, pat, &j, MAXPAT);
    }
    (mark(9, 21), lastj = lj);
    if ((!done))
      (mark(9, 22), i = i + 1);
  }
  junk = (mark(9, 23), addstr(ENDSTR, pat, &j, MAXPAT));
  if ((done) || ((mark(9, 24), arg[i] != delim)))
    (mark(9, 25), result = 0);
  else if (((mark(9, 26), !junk)))
    (mark(9, 27), result = 0);
  else
    (mark(9, 28), result = i);
  MARK(9, 29);
  return result;
}

int getpat(char *arg, char *pat) {
  MARK(10, 1);
  int makeres;
  int result;

  makeres = makepat(arg, 0, ENDSTR, pat);
  result = (makeres > 0);
  MARK(10, 2);
  return result;
}

int makesub(char *arg, int from, char delim, char *sub) {
  MARK(11, 1);
  int result;
  int i, j;
  int junk;
  char escjunk;

  j = 0;
  i = from;
  while (((MARK(11, 2), arg[i] != delim)) &&
         ((mark(11, 3), arg[i] != ENDSTR))) {
    if ((mark(11, 4), arg[i] == (unsigned)('&')))
      junk = (mark(11, 5), addstr(DITTO, sub, &j, MAXPAT));
    else {
      escjunk = (mark(11, 6), esc(arg, &i));
      junk = addstr(escjunk, sub, &j, MAXPAT);
    }
    (mark(11, 7), i = i + 1);
  }
  if ((mark(11, 8), arg[i] != delim))
    (mark(11, 9), result = 0);
  else {
    junk = (mark(11, 10), addstr(ENDSTR, &(*sub), &j, MAXPAT));
    if ((!junk))
      (mark(11, 11), result = 0);
    else
      (mark(11, 12), result = i);
  }
  MARK(11, 13);
  return result;
}

int getsub(char *arg, char *sub) {
  MARK(12, 1);
  int makeres;
  int result;

  makeres = makesub(arg, 0, ENDSTR, sub);
  result = (makeres > 0);
  MARK(12, 2);
  return result;
}

int locate(char c, char *pat, int offset) {
  MARK(13, 1);
  int i;
  int flag;

  flag = false;
  i = offset + pat[offset];
  while (((MARK(13, 2), i > offset))) {
    if ((mark(13, 3), c == pat[i])) {
      (mark(13, 4), flag = true);
      i = offset;
    } else
      (mark(13, 5), i = i - 1);
  }
  MARK(13, 6);
  return flag;
}

int omatch(char *lin, int *i, char *pat, int j) {
  MARK(14, 1);
  char advance;
  int result;

  advance = -1;
  if (lin[*i] == ENDSTR)
    (mark(14, 2), result = false);
  else {
    if (!(mark(14, 3), in_pat_set(pat[j]))) {
      (void)(mark(14, 4), zop_fprintf1(stdout, "in omatch: can't happen\n"));
      MARK(14, 24);
      abort();
    } else {
      switch ((mark(14, 19), pat[j])) {
      case LITCHAR:
        if ((mark(14, 5), lin[*i] == pat[j + 1]))
          (mark(14, 6), advance = 1);
        break;
      case BOL:
        if ((mark(14, 7), *i == 0))
          (mark(14, 8), advance = 0);
        break;
      case ANY:
        if ((mark(14, 9), lin[*i] != NEWLINE))
          (mark(14, 10), advance = 1);
        break;
      case EOL:
        if ((mark(14, 11), lin[*i] == NEWLINE))
          (mark(14, 12), advance = 0);
        break;
      case CCL:
        if ((mark(14, 13), locate(lin[*i], pat, j + 1)))
          (mark(14, 14), advance = 1);
        break;
      case NCCL:
        if (((mark(14, 15), lin[*i] != NEWLINE)) &&
            (!(mark(14, 16), locate(lin[*i], pat, j + 1))))
          (mark(14, 17), advance = 1);
        break;
      default:
        (mark(14, 18), Caseerror(pat[j]));
      };
    }
  }
  if (((mark(14, 20), advance >= 0))) {
    (mark(14, 21), *i = *i + advance);
    result = true;
  } else
    (mark(14, 22), result = false);
  MARK(14, 23);
  return result;
}

int patsize(char *pat, int n) {
  MARK(15, 1);
  int size;
  if (!in_pat_set(pat[n])) {
    (void)(mark(15, 2), zop_fprintf1(stdout, "in patsize: can't happen\n"));
    MARK(15, 10);
    abort();
  } else
    switch ((mark(15, 8), pat[n])) {
    case LITCHAR:
      (mark(15, 3), size = 2);
      break;

    case BOL:
    case EOL:
    case ANY:
      (mark(15, 4), size = 1);
      break;
    case CCL:
    case NCCL:
      (mark(15, 5), size = pat[n + 1] + 2);
      break;
    case CLOSURE:
      (mark(15, 6), size = CLOSIZE);
      break;
    default:
      (mark(15, 7), Caseerror(pat[n]));
    }
  MARK(15, 9);
  return size;
}

int amatch(char *lin, int offset, char *pat, int j) {
  MARK(16, 1);
  int i;
  int k;
  int result;
  int done;
  int size;

  done = false;
  while (((MARK(16, 2), !done)) && ((mark(16, 3), pat[j] != ENDSTR)))
    if ((mark(16, 4), pat[j] == CLOSURE)) {
      j = j + (mark(16, 5), patsize(pat, j));
      i = offset;
      while (((MARK(16, 6), !done)) && ((mark(16, 7), lin[i] != ENDSTR))) {
        result = (mark(16, 8), omatch(lin, &i, pat, j));
        if (!result)
          (mark(16, 9), done = true);
      }
      (mark(16, 10), done = false);
      while (((MARK(16, 11), !done)) && ((mark(16, 12), i >= offset))) {
        size = (mark(16, 13), patsize(pat, j));
        k = amatch(lin, i, pat, j + size);
        if ((k >= 0))
          (mark(16, 14), done = true);
        else
          (mark(16, 15), i = i - 1);
      }
      (mark(16, 16), offset = k);
      done = true;
    } else {
      result = (mark(16, 17), omatch(lin, &offset, pat, j));
      if ((!result)) {
        (mark(16, 18), offset = -1);
        done = true;
      } else
        j = j + (mark(16, 19), patsize(pat, j));
    }
  MARK(16, 20);
  return offset;
}

void putsub(char *lin, int s1, int s2, char *sub) {
  MARK(17, 1);
  int i;
  int j;

  i = 0;
  while (((MARK(17, 2), sub[i] != ENDSTR))) {
    if ((mark(17, 3), sub[i] == DITTO))
      for ((mark(17, 4), j = s1); (MARK(17, 5), j < s2); (mark(17, 7), j++)) {
        (mark(17, 6), fputc(lin[j], stdout));
      }
    else {
      (mark(17, 8), fputc(sub[i], stdout));
    }
    (mark(17, 9), i = i + 1);
  }
  MARK(17, 10);
}

void subline(char *lin, char *pat, char *sub) {
  MARK(18, 1);
  int i;
  int lastm;
  int m;

  lastm = -1;
  i = 0;
  while (((MARK(18, 2), lin[i] != ENDSTR))) {
    m = (mark(18, 3), amatch(lin, i, pat, 0));
    if ((m >= 0) && ((mark(18, 4), lastm != m))) {
      (mark(18, 5), putsub(lin, i, m, sub));
      lastm = m;
    }
    if (((mark(18, 6), m == -1)) || ((mark(18, 7), m == i))) {
      (mark(18, 8), fputc(lin[i], stdout));
      i = i + 1;
    } else
      (mark(18, 9), i = m);
  }
  MARK(18, 10);
}

void change(char *pat, char *sub) {
  MARK(19, 1);
  string line;
  int result;

  result = my_getline(line, MAXSTR);
  while ((MARK(19, 2), (result))) {
    (mark(19, 3), subline(line, pat, sub));
    result = my_getline(line, MAXSTR);
  }
  MARK(19, 4);
}

int main(int argc, char *argv[]) {
  MARK(20, 1);
  string pat;
  string sub;
  int result;

  if (argc < 2) {
    (void)(mark(20, 2), zop_fprintf1(stdout, "usage: change from [to]\n"));
    MARK(20, 11);
    exit(1);
  };

  result = (mark(20, 3), getpat(argv[1], pat));
  if (!result) {
    (void)(mark(20, 4), zop_fprintf1(stdout, "change: illegal \"from\" pattern\n"));
    MARK(20, 12);
    exit(2);
  }

  if ((mark(20, 5), argc >= 3)) {
    result = (mark(20, 6), getsub(argv[2], sub));
    if (!result) {
      (void)(mark(20, 7), zop_fprintf1(stdout, "change: illegal \"to\" string\n"));
      MARK(20, 13);
      exit(3);
    }
  } else {
    (mark(20, 8), sub[0] = '\0');
  }

  (mark(20, 9), change(pat, sub));
  MARK(20, 10);
  return 0;
}

void Caseerror(int n) {
  (void)(MARK(21, 1), zop_fprintf2(stdout, "Missing case limb: line %d\n", n));
  MARK(21, 2);
  exit(4);
}

