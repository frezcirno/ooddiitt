#include <stdio.h>
#include <stdlib.h>
#include "mark.h"

void foo(int n) {
  MARK(1, 3);

  int index;
  for (index = 0; (MARK(1, 2), index < 3); ++index) {
    printf("Hello");
  }
  MARK(1,1);
}
