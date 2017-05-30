#include "mark.h"
/*  -*- Last-Edit:  Wed May 7 10:12:52 1993 by Monica; -*- */

#include <stdio.h>
#include <stdlib.h>

/* A job descriptor. */

#define NEW_JOB 1
#define UPGRADE_PRIO 2
#define BLOCK 3
#define UNBLOCK 4
#define QUANTUM_EXPIRE 5
#define FINISH 6
#define FLUSH 7

#define MAXPRIO 3
#define RATIO_QUANTA 256

typedef struct _job {
  struct _job *next, *prev; /* Next and Previous in job list. */
  int val;                  /* Id-value of program. */
  short priority;           /* Its priority. */
} Ele, *Ele_Ptr;

typedef struct list { /* doubly linked list */
  Ele *first;
  Ele *last;
  int mem_count; /* member count */
} List;


/*-----------------------------------------------------------------------------
  del_ele
        deletes the old_ele from the list.
        Note: even if list becomes empty after deletion, the list
              node is not deallocated.
-----------------------------------------------------------------------------*/
List *del_ele(List *d_list, Ele *d_ele) {
  if ((MARK(5, 10), !d_list) || (mark(5, 9), !d_ele)) {
    return (MARK(5, 8), (NULL));
  }

  if ((mark(5, 7), d_ele->next)) {
    (mark(5, 6), d_ele->next->prev = d_ele->prev);
  } else {
    (mark(5, 5), d_list->last = d_ele->prev);
  }
  if ((mark(5, 4), d_ele->prev)) {
    (mark(5, 3), d_ele->prev->next = d_ele->next);
  } else {
    (mark(5, 2), d_list->first = d_ele->next);
  }
  /* KEEP d_ele's data & pointers intact!! */
  d_list->mem_count--;
  return (MARK(5, 1), (d_list));
}

