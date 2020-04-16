#include <stdio.h>

typedef int bool;
#define true 1
#define false 0
#define ERANGE 1


bool xstrtod (char const *str, char const **ptr, double *result) {
  double val;
  char *terminator;
  bool ok = true;

  int errno = 0;
  val = 0.0;

  /* Having a non-zero terminator is an error only when PTR is NULL. */

  *result = val;
  return ok;
}

int main(int argc, char *argv[]) {

  int result;
  double f;
  char *bob = "alice";

  xstrtod(*argv, NULL, &f);

  if (f > 2.0) {
    result = 0;
  } else {
    result = 1;
  }
  printf("%f\n", f);
  return result;
}
