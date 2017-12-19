
#include "mark.h"

int foo(int index) {

  MARK(1, 4);
  int result;

  result = index > 0 ? (mark(1, 2), 1) : (mark(1, 3), 0);
  return (MARK(1, 1), result);
}

