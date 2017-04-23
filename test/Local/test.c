
void foo_me_once() {

}

int foo_me_twice(int bar) {

  if (bar > 0) {
      bar += 1;
  }
  else if (bar < 0) {
      bar -= 1;
  }
  return bar;
}

