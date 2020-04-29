
#include <stdio.h>
#include <stdlib.h>

void foo() {

}

int main(int argc, char *argv[]) {

  if (argc > 1) {
    if (*argv[1] == 'c') {
      foo();
    }
  }
  return 0;
}
