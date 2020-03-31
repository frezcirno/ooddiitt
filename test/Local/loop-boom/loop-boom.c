
#include <stdio.h>

#define BUFFER_SIZE 32
char buffer[BUFFER_SIZE];

void boom() {
  for (unsigned idx = 0; idx < BUFFER_SIZE; ++idx) {
    if (buffer[idx] == 0) {
      puts("0");
    } else {
      puts("1");
    }
  }
  puts("\n");
}

int main(int argc, char *argv[]) {
  boom();
  return 0;
}
