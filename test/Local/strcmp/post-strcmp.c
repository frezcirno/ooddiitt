#include <stdio.h>
#include <string.h>

int foo1() {

  int ret = 0;
  ret += strcmp("hello", "hello");  
  ret += strcmp("hello", "goodbye");  
  return ret + 2;
}

int foo2(char *arg) {

  int ret = 0;
  ret += strcmp(arg, "hello");  
  ret += strcmp(arg, "goodbye");  
  return ret + 2;
}

int foo3(char *arg) {
    
  int ret = 0;
  ret += strcmp("hello", arg);  
  ret += strcmp("goodbye", arg);  
  return ret + 2;
}

int foo4(char *arg1, char *arg2) {

  int ret = 0;
  ret += strcmp(arg1, arg2);  
  ret += strcmp(arg2, arg1);  
  return ret + 2;
}

int main(int argc, char *argv[]) {

  foo1();
  foo2("hello");
  foo3("hello");
  foo4("hello", "goodbye");
  return 0;
}

