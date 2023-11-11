
#include <stdio.h>
#include <stdlib.h>

int foo(char *bar) {

  int result = atoi(bar) * 2;
  return result;
}

unsigned changed_gb = 0;
int removed_gb = 5;
void removed_fn() {

}

void changed_sig_fn(int i) {

}

typedef struct {
  unsigned m1;
  unsigned m2;
} bob_t;

void changed_arg_ptr(bob_t *bob) {
  printf("%u\n", bob->m1);
}

int main(int argc, char *argv[]) {

  int exit_code = 1;
  removed_fn();
  changed_sig_fn(1);
  bob_t bob;
  changed_arg_ptr(&bob);

  if (argc != 2) {
    printf("usage: %s arg\n", argv[0]);
  } else {
    printf("result=%d\n", foo(argv[1]));
    exit_code = 0;
  }
  return exit_code;
}
