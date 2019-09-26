

int main(int argc, char *argv[]) {

  int ret = 0;
  for (int index = 0; index < argc; index++) {
    if (*argv[index] == 'y') {
      ret += 1;
    }
  }
  return ret;
}