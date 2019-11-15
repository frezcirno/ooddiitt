
void foo(int bar) {

}

int global_int = 0;

int main(int argc, char *argv[]) {

  while (**(++argv) == 'a') {
    foo(--argc);
  }
  return 0;
}

