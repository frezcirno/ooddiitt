
#include <stdio.h>
#include <stdlib.h>

int foo(char *bar) {

  int result = atoi(bar) * 3;
  return result;
}

int main(int argc, char *argv[]) {

  int exit_code = 1;
  if (argc != 2) {
    printf("usage: %s arg\n", argv[0]);
  } else {
    printf("result=%d\n", foo(argv[1]));
    exit_code = 0;
  }
  return exit_code;
}
