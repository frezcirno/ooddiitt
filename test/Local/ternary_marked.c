
#include "mark.h"

int bar() {
  return (MARK(1, 2), (MARK(1, 1), 0));
}

int foo(int index) {

  MARK(2, 10);
  int result;
  int *special = &result;
  int ignored = 0;
  int counter;
  for (counter = 0; (MARK(2, 9), counter < 32); (mark(2, 5), ++counter)) {
    if ((mark(2, 8), bar()) > 0) {
      (mark(2, 7), ignored += 1);
    } else {
      (mark(2, 6), ignored -= 1);
    }
  }

  *special = (mark(2, 4), index > 0) ? (mark(2, 2), 1) : (mark(2, 3), 0);
  return (MARK(2, 1), *special);
}
