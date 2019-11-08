

int foo00(int *bar) {

  int result = 0;
  if (*bar > 0) result = 1;
  else if (*bar < 0) result = -1;
  return result;
}
