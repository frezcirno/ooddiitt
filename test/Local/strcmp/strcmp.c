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

int false = 0;
char buffer[4096];

int foo5() {
  int ret = strcmp(buffer, "Lorem ipsum dolor sit amet, in quod pertinax philosophia usu, ut pri clita quaeque appareat, ad inani ignota melius pro. Erant percipitur ut eam, at vidisse urbanitas eam. Nec ad essent senserit accommodare, vidit gloriatur et sea. Nec eu alia aliquid, latine percipitur ne vim, vis aperiam gubergren democritum ne. Delicata postulant expetenda mel ei. Commodo utroque accumsan sed ad, no option fabellas vix, dicat apeirian evertitur te mei. Mei sumo natum phaedrum cu, probo accusata pro et, his liber lucilius ea.");
  return ret;
}

int main(int argc, char *argv[]) {


  int ret = 0;
  if (false) {
    foo1();
    foo2("hello");
    foo3("hello");
    foo4("hello", "goodbye");
    foo5();
  }
  return ret;
}

