#include <stdio.h>

int main(int argc, char *argv[]) {

  for (int idx = 0; idx < argc; ++idx) {
    printf("%s\n", argv[idx]);
  }
  return 0;
}
