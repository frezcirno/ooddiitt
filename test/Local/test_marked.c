#include "mark.h"

int bar() {
  {
    MARK(1, 2);
    int result_e97a08b91f = 0;
    return (MARK(1, 1), (result_e97a08b91f));
  };
}

int foo() {

  MARK(2, 7);
  int index;
  int result = 0;
  for (index = 0; (MARK(2, 6), index < 32); (mark(2, 2), ++index)) {
    if ((mark(2, 5), bar())) {
      (mark(2, 4), result += 1);
    } else {
      (mark(2, 3), result -= 1);
    }
  }
  return (MARK(2, 1), result);
}
