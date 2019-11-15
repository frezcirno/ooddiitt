
#include <stdio.h>
#include <klee/pg-klee.h>

int my_global;

int main(int argc, char *argv[]) {

  klee_message(argv[0]);


  // for (int index = 1; index < argc; index++) {
  //   if (*argv[index] == 'y') {
  //     klee_message("yes");
  //   } else {
  //     klee_message("no");
  //   }
  // }

  // int ret = 0;
  // for (int index = 0; index < argc; index++) {
  //   if (*argv[index] == 'y') {
  //     ret += 1;
  //   }
  // }
  return 0;
}
