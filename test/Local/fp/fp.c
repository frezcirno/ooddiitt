#include <stdio.h>
#include <math.h>

int main(int argc, char *argv[]) {

  double d1 = -4.75;
  double d2 = floor(d1);
  double d3 = rint(d1);
  double d4;
  double d5 = modf(d1, &d4);
  double d6 = fabs(d1);
  printf("floor=%f\n", d2);
  printf("rint=%f\n", d3);
  printf("modf=%f,%f\n", d4, d5);
  printf("fabs=%f\n", d6);
  return 0;
}