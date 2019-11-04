#include <stdlib.h>

void bar() __attribute__ ((noreturn));

void bar() {

}

void foo00() {
  bar();
}
