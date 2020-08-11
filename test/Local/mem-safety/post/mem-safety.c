
char get_letter(unsigned idx) {

  static char *msg = "Hello";
  char result = 0;
  result = msg[idx];
  return result;
}

int main(int argc, char *argv[]) {

  char ch = get_letter(argc);
  return ch;
}
