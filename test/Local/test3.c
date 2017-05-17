#include "mark.h"

void bar();

void foo(int flag) {

  if ((MARK(1, 5), flag)) {
    while ((MARK(1, 4), !flag)) {
      (mark(1, 3), bar());
    }
  }
  MARK(1, 1);
  return;
}
