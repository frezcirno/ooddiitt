#include "mark.h"
/* Generated by CIL v. 1.7.3 */
/* print_CIL_Input is true */

typedef unsigned long uintptr_t;
struct bar {
  unsigned int us;
};
extern void pgklee_hard_assume(uintptr_t condition);
char buffer[10];
void annot_foo1(int index);
char foo1(int index) {
  MARK(1, 2);
  char result;

  {
    annot_foo1(index);
    result = buffer[index];
    return (MARK(1, 1), (result));
  }
}
void annot_foo1(int index) {

  {
    (MARK(2, 2), pgklee_hard_assume(index >= 0));
    pgklee_hard_assume(index < 10);
    MARK(2, 1);
    return;
  }
}
void foo2(struct bar *b) {

  {
    MARK(3, 2);
    MARK(3, 1);
    return;
  }
}
void annot_foo2(struct bar *b) {

  {
    MARK(4, 2);
    MARK(4, 1);
    return;
  }
}
void annot_bar(struct bar *b) {

  {
    MARK(5, 2);
    MARK(5, 1);
    return;
  }
}
