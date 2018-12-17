
#include "../../../include/klee/invariants.h"

struct bar {
  unsigned int us;
};


char buffer[10];

void annot_foo1(int index);


char foo1(int index) {

  annot_foo1(index);
  char result;
  result = buffer[index];
  return result;
}

void annot_foo1(int index) {

  pgklee_hard_assume(index >= 0);
  pgklee_hard_assume(index < 10);
}

void foo2(struct bar *b) {

  

}

void annot_foo2(struct bar *b) {

}

void annot_bar(struct bar *b) {

  
}

