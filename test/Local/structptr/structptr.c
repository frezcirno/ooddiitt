#include <stdio.h>

struct bar {
  unsigned bar1;
  unsigned bar2;
};

void foo01(struct bar *arg) {

  char *msg;
  if (arg->bar2 == 0) {
    msg = "no";
  } else {
    msg = "yes";
  }
  printf("%s\n", msg);
}
