
int sum(int i, int j) {
  return i + j;
}

void foo00() {

  int (*fp)(int i, int j) = sum;
  int result = fp(1, 2);

}

void foo01(int (*fp)(int i, int j)) {

  int result = fp(1, 2);

}



