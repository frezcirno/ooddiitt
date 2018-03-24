

int main(int argc, char *argv[]) {

  int result = 0;
  if (argc == 1) {
    result = 10;
  } else if (argc == 2) {
    result = 50;
  } else {
    result = 51;
  }

  return result;
}

