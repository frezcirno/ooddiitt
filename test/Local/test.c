
int bar() {
  return 0;
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

