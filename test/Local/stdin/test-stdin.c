

#include <stdio.h>

int main(int argc, char *argvp[]) {

  int c = getc(stdin);
  if (c == 'a') {
    printf("give me an 'A'!\n");
  } else {
    printf("or not...\n");
  }
  return 0;
}
