

char *strcpy(char *dest, const char *source) {

  char *ptr = dest;
  while (*source != '\0') {
    *(ptr++) = *(source++);
  }
  return dest;
}
