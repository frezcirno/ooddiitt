
int sum(char *str, int i, int j) {
  return i + j;
}

int product(char *str, int i, int j) {
  return i * j;
}

// int (*fp)(char *, int, int);
// char *bar="bar";
int integer = 0;

int foo1() {

  int result = 0;
  if (integer > 0) {
    result = 2;
  } else if (integer < 0) {
    result = -2;
  }
  return result;
}

// int foo2(void) {
//   return 0;  
// }

// int foo3(void) {

//   int result = fp(bar, 1, 2);
//   return result;
// }

int main(int argc, char *argv[]) {

  foo1();
  // foo2();

  // fp = sum;
  // int i1 = foo3();
  // fp = product;
  // int i2 = foo3();
  return 0;
}
