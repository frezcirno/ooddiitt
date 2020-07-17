
#include <stdio.h>
#include <stdlib.h>

int foo(char *bar) {

  int result = atoi(bar) * 3;
  return result;
}

unsigned long changed_gb = 0;
int added_gb = 5;
void added_fn() {

}

void changed_sig_fn(long i) {

}

typedef struct {
  unsigned m1;
  unsigned long m2;
} bob_t;

void changed_arg_ptr(bob_t *bob) {
  printf("%u\n", bob->m1);
}

int main(int argc, char *argv[]) {

  int exit_code = 1;
  added_fn();
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
