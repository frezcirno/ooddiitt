
#include <stdio.h>
#include <string.h>

char message[] = "Goodbye cruel world";

int main(int argc, char *argv[]) {

  char buffer[256];
  memcpy(buffer, message, sizeof(message) + 1);
  printf("%s\n", buffer);
  return 0;
}
