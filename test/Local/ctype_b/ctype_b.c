#include <ctype.h>

int foo(int c) {

  int result = 0;
  if (isdigit(c)) {
    result = 1;
  } else if (isalpha(c)) {
    result = 2;
  }
  return result;
}
