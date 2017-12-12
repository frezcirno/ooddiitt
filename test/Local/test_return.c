
int bar() {
  {
    int result_e97a08b91f = 0;
    return (result_e97a08b91f);
  };
}

int foo() {

  int index;
  int result = 0;
  for (index = 0; index < 32; ++index) {
    if (bar()) {
      result += 1;
    } else {
      result -= 1;
    }
  }
  return result;
}
