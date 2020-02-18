
#include <stdio.h>

int gbar;

int foo01(unsigned bar) {
  gbar = bar + 1;
  return gbar;
}

int foo02(unsigned bar) {
  gbar = bar + 1;
  return gbar;
}

int foo03(unsigned bar) {
  gbar = bar + 1;
  return gbar;
}

int main(int argc, char *argv[]) {

  for (int idx = 0; idx < argc; ++idx) {
    printf("%s\n", argv[idx]);
  }
  return 0;
}

