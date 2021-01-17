#include <stdio.h>
#include <locale.h>

void foo1(int arg) {
  int z;  
  setlocale(LC_ALL, "");
  z = arg * 4;
  printf("%i\n", z);
}

void foo2(int arg) {
  int z;  
  z = arg * 4;
  printf("%i\n", z);
}

int main(int argc, char *argv[]) {
  foo1(2);
  foo2(2);
  return 0;
}
