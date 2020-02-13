
#include <stdio.h>

int foo00(int *bar) {

  int result = 0;
  if (*bar > 0) result = 1;
  else if (*bar < 0) result = -1;
  return result;
}

int main(int argc, char *argv[]) {

  while (*argv != NULL) {
    printf("%s\n", *argv++);
  }
  if (foo00(&argc) == 0) {
    printf("toto, I don't think we're in Kansas anymore...\n");
  }
  return 0;
}
