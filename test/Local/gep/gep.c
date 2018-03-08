
#include <mark.h>

#define LENGTH 16
char buffer[LENGTH];

void msg(const char *msg) {
}

void foo(unsigned short index) {

  char *ptr = (void *) 0;
  char ele;

  // should constrain index 0 .. LENGTH - 1
  ptr = &buffer[index];

  if (index < LENGTH) {
    buffer[0] = 0;
  } else {
    buffer[0] = 1;
  }

  // should be able to construct a pointer to anywhere
  ptr = &buffer[LENGTH * 2];

  // but reading or writing should terminate
  // if (index % 2) {
  //   *ptr = '#';
  // } else {
  //   ele = *ptr;
  // }
}

