#include <stdio.h>

int gbar;

typedef struct {
  int bob;
  int jane;
} my_struct;

unsigned *pbar;
my_struct sbar;
char abar[10];
void (*fpbar)(unsigned);

int foo01(unsigned bar) {
  gbar = bar + 1;
  return gbar;
}

int foo02(unsigned bar) {
  gbar = bar + 1;
  return gbar + 1;
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