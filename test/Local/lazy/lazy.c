#include <stdio.h>

int foo00(int i) {

  int result = 0;
  if (i > 0) {
    result = 1;
  } else if (i < 0) {
    result = -1;
  }
  return result;
}

int foo01(int *ptr) {

  int result;
  if (ptr == NULL) {
    result = 1;
  } else {
    result = *ptr + 1;
  }
  return result;
}

int foo02(int (*ptr)()) {

  int result;
  if (ptr == NULL) {
    result = 1;
  } else {
    result = (*ptr)() + 1;
  }
  return result;
}

typedef struct {
  int f1;
  int f2;
} bar03_t;

int foo03(bar03_t *ptr) {

  int result = 0;
  if (ptr == NULL) {
    result += 0;
  } else {
    if (ptr->f1 > 0) {
      result += 1;
    } else  if (ptr->f1 < 0) {
      result -= 1;
    }
    if (ptr->f2 > 0) {
      result += 10;
    } else if (ptr->f2 < 0) {
      result -= 10;
    }
  }
  return result;
}

typedef struct {
  int f1;
  int (*f2)();
} bar04_t;

int foo04(bar04_t *ptr) {

  int result = 0;
  if (ptr == NULL) {
    result += 0;
  } else {
    if (ptr->f1 > 0) {
      result += 1;
    } else  if (ptr->f1 < 0) {
      result -= 1;
    }
    if (ptr->f2 == NULL) {
      result += 10;
    } else {
      result -= 10;
    }
  }
  return result;
}

typedef struct {
  char *f1;
  char *f2;
} bar05_t;

int foo05(bar05_t *ptr) {

  int result = 0;
  if (ptr == NULL) {
    result += 0;
  } else {
    if (ptr->f1 != NULL) {
      result += 1;
    } else {
      result -= 1;
    }
    if (ptr->f2 == NULL) {
      result += 10;
    } else {
      result -= 10;
    }
  }
  return result;
}

int foo06(char *ptr[2]) {

  int result = 0;
  if (ptr == NULL) {
    result += 0;
  } else {
    if (ptr[0] != NULL) {
      result += 1;
    } else {
      result -= 1;
    }
    if (ptr[1] != NULL) {
      result += 10;
    } else {
      result -= 10;
    }
  }
  return result;
}
