
#include <stdio.h>

int main(int argc, char *argv[]) {

  while (*argv != NULL) {
    printf("%s\n", *argv++);
  }
  return 0;
}


int foo00(int *bar) {

  int result = 0;
  if (*bar > 0) result = 1;
  else if (*bar < 0) result = -1;
  return result;
}
