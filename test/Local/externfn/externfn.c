#include <stdlib.h>
#include <stdio.h>

int foo(const char *arg1);

const char const_string[] = "1234";
extern const char extconst_string[];

int bar(const char *arg1) {
  (void) extconst_string;
  return 0;
}

int main(int argc, char *argv[]) {

  char string[] = "0";

  bar(string);
  int val = foo(string);
  if (val > 0) {
    printf("positive\n");
  } else if (*string != '0') {
    printf("negative\n");
  }
  return 0;
}
