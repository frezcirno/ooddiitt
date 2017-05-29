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

List *del_ele(List *d_list, Ele *d_ele);

int alloc_proc_num;
int num_processes;
Ele *cur_proc;
List *prio_queue[MAXPRIO + 1]; /* 0th element unused */
List *block_queue;

void schedule(usher_t *usher) {
  MARK(9, 6);
  int i;

  cur_proc = NULL;
  for (i = MAXPRIO; (MARK(9, 5), guide(usher, i > 0)); (mark(9, 2), i--)) {
    if ((mark(9, 4), guide(usher, prio_queue[i]->mem_count > 0))) {
      cur_proc = prio_queue[i]->first;
      prio_queue[i] = del_ele(prio_queue[i], cur_proc);
      MARK(9, 3);
      return;
    }
  }
  MARK(9, 1);
  return;
}
