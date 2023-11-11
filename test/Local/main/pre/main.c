
#include <stdio.h>
#include <stdlib.h>

int foo(int i) {
  return i + 1;
}

int main(int argc, char *argv[]) {

  if (argc > 1) {
    if (*argv[1] == 'c') {
      foo(42);
    }
  }
  return 0;
}
