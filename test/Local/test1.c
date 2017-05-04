#include <stdlib.h>

int fighter = 0;

void foo_me_once() {
 
  if (fighter > 0) {
    fighter += 1;
  } else if (fighter < 0) {
    fighter -= 1;
  }
}

int foo_me_twice(int bar) {

  if (bar > 0) {
    bar += 1;
  } else if (bar < 0) {
    bar -= 1;
  }
  return bar;
}

void foo_me_thrice(int bar) {
  
  int bar2 = foo_me_twice(bar);

  if (bar2 > 0) {
    bar2 += 1;
  } else if (bar2 < 0) {
    bar2 -= 1;
  }
}

void foo_me_quadice(char *bar) {

  if (*bar == '\0') {
    *bar = '\n';
  } else if (*bar == '\n') {
    *bar = '\0';
  }
}

void foo_me_quinice() {

  char buffer[64];
  foo_me_quadice(buffer);
}

void foo_me_sextice() {

  char *buffer = malloc(64);
  foo_me_quadice(buffer);
  free(buffer);
}

/* sext, sept, oct, non, dec, */

int main(int argc, char *argv[]) {

  return 0;
}


