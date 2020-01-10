#include <stdlib.h>
#include <stdio.h>

void bar() {

}

void foo00() {
  bar();
}

void foo01(int num) {
  printf("Hello %d\n", num);
}

int foo02() {

  int result = 0;
  int ch = getchar();
  if (ch == 'a') {
    result = 1;
  }
  return result;
}