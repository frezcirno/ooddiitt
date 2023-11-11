#include <stdio.h>
#include <locale.h>

void foo1(int arg) {
  int z;  
  setlocale(LC_ALL, "");
  z = arg * 2;
  printf("%i\n", z);
}

void foo2(int arg) {
  int z;  
  z = arg * 2;
  printf("%i\n", z);
}

int main(int argc, char *argv[]) {
  foo1(1);
  foo2(1);
  return 0;
}
