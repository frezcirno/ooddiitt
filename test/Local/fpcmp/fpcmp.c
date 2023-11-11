#include <stdio.h>
#include <stdlib.h>

typedef int bool;
#define true 1
#define false 0
#define ERANGE 1


bool xstrtod (char const *str, char const **ptr, double *result) {
  double val;
  bool ok = true;

  val = atof(str);

  *result = val;
  return ok;
}

int main(int argc, char *argv[]) {

  int result = 0;
  double f;

  for (unsigned idx = 0; idx < argc; ++idx) {
    if (xstrtod(argv[idx], NULL, &f)) {
      printf("%u: %f\n", idx, f);
    } else {
      printf("%u: not a number\n", idx);
    }
  }
  return result;
}
