#include <stdlib.h>
#include <stdio.h>

int foo(const char *arg1, char *arg2);

void bar(char *string) {

  int val;
  const char *msg = NULL;

  for (unsigned counter = 0; counter < 3; ++counter) {
    val = foo(string, string);
    msg = NULL;
    if (val > 0) {
      msg = "positive";
    } else if (*string != '0') {
      msg = "negative";
    } else {
      msg = "?";
    }
    if (msg != NULL) {
      printf("%s\n", msg);
    }
  }
}

int main(int argc, char *argv[]) {

  char string[] = "0";
  bar(string);
  return 0;
}
