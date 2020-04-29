
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[]) {

  if (argc > 0) {
    *argv[1] = 'b';
  }
  return 1;
}
