
int bar() {
  {
    int result_82dcf109c9 = 0;
    return (result_82dcf109c9);
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
