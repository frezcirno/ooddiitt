
int test(void);

int bar(int i, int *ii, int **iii, int ***iiii);

void foo() {

  int a;
  int *b = &a;
  int **c = &b;
  int ***d = &c;

  bar(a, b, c, d);
  if (*b > 0) {
    test();
  } else if (*b < 0) {
    test();
  }
  test();
}
