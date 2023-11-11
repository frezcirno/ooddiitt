#include <stdio.h>

void foo(int val) {

  if (val < 0) {
    printf("minus\n");
  } else if (val > 0) {
    printf("plus\n");
  } else {
    printf("neither\n");
  }
}

int main(int argc, char *argv[]) {

  foo(1);
  return 0;
}