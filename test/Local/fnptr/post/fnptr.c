
int sum(int i, int j) {
  return i + j;
}

int product(int i, int j) {
  return i * j;
}

int (*fp)(int, int);

int foo(void) {

  int result = fp(1, 2);
  return result;
}

int entry() {

  int result = 0;
  result = foo();
  return result;
}

int main(int argc, char *argv[]) {
  fp = product;
  fp = sum;

  entry();
  return 0;
}
