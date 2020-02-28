
#include <stdio.h>
#include <stdlib.h>

int gbar;

typedef struct {
  int bob;
  int jane;
} my_struct;

unsigned *pbar;
my_struct sbar;
char abar[10];
void (*fpbar)(unsigned);

void noop(int arg) {
  return;
}

int foo01(unsigned bar) {
  gbar = bar + 1;
  return gbar;
}

int foo02(unsigned bar) {
  gbar = bar + 1;
  return gbar;
}

int foo03(unsigned bar) {
  noop(bar);
  gbar = bar + 1;
  return gbar;
}

int main(int argc, char *argv[]) {

  for (int idx = 0; idx < argc; ++idx) {
    printf("%s\n", argv[idx]);
  }
  exit(0);
}

char *foo04(unsigned bar) {
  return NULL;
}

