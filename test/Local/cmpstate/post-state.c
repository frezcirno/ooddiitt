#include <stdio.h>

int gbar;

int foo01(unsigned bar) {
  gbar = bar + 1;
  return gbar;
}

int foo02(unsigned bar) {
  gbar = bar + 2222;
  return gbar;
}

int foo03(unsigned bar) {
  return bar + 1;
}

int main(int argc, char *argv[]) {

  for (int idx = 0; idx < argc; ++idx) {
    if (idx == 3) {
      printf("bob\n");
    } else {
      printf("%s\n", argv[idx]);
    }
  }
  return argc <= 4 ? 0 : 1;
}
