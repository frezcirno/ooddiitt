

int main(int argc, char *argv[]) {

  int ret = 0;
  int index;
  for (index = 0; index < argc; index++) {
    if (*argv[index] == 'y') {
      ret = 1;
    }
  }
  return ret;
}