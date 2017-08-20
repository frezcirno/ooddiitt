
#include "mark.h"

int bar() { return (MARK(1, 13), (MARK(1, 1), 0)); }
void magic(int j);

void foo() {

  MARK(2, 7);
  unsigned index;
  int value;
  for (index = 0; (MARK(2, 6), index < 32); (mark(2, 2), ++index)) {
    if ((mark(2, 5), bar())) {
      (mark(2, 4), magic(value + 1));
    } else {
      (mark(2, 3), magic(value - 1));
    }
  }
  MARK(2, 1);
  return;
}
