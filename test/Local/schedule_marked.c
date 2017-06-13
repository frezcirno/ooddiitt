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

void schedule(void);

Ele *new_ele(int new_num);
List *new_list(void);
List *append_ele(List *a_list, Ele *a_ele);
List *del_ele(List *d_list, Ele *d_ele);

/*-----------------------------------------------------------------------------
  new_ele
     alloates a new element with value as num.
-----------------------------------------------------------------------------*/
Ele *new_ele(int new_num) {
  MARK(1, 1);
  Ele *ele;

  ele = (Ele *)malloc(sizeof(Ele));
  ele->next = NULL;
  ele->prev = NULL;
  ele->val = new_num;
  return (MARK(1, 13), ele);
}

/*-----------------------------------------------------------------------------
  new_list
        allocates, initializes and returns a new list.
        Note that if the argument compare() is provided, this list can be
            made into an ordered list. see insert_ele().
-----------------------------------------------------------------------------*/
List *new_list(void) {
  MARK(2, 1);
  List *list;

  list = (List *)malloc(sizeof(List));

  list->first = NULL;
  list->last = NULL;
  list->mem_count = 0;
  return (MARK(2, 13), (list));
}

/*-----------------------------------------------------------------------------
  append_ele
        appends the new_ele to the list. If list is null, a new
        list is created. The modified list is returned.
-----------------------------------------------------------------------------*/
List *append_ele(List *a_list, Ele *a_ele) {
  if ((MARK(3, 6), !a_list)) {
    a_list = (mark(3, 5), new_list()); /* make list without compare function */
  }

  (mark(3, 4), a_ele->prev = a_list->last); /* insert at the tail */
  if (a_list->last) {
    (mark(3, 3), a_list->last->next = a_ele);
  } else {
    (mark(3, 2), a_list->first = a_ele);
  }
  a_list->last = a_ele;
  a_ele->next = NULL;
  a_list->mem_count++;
  return (MARK(3, 1), (a_list));
}


/*-----------------------------------------------------------------------------
  find_nth
        fetches the nth element of the list (count starts at 1)
-----------------------------------------------------------------------------*/
Ele *find_nth(List *f_list, int n) {
  MARK(4, 8);
  Ele *f_ele;
  int i;

  if (!f_list) {
    return (MARK(4, 7), NULL);
  }
  (mark(4, 6), f_ele = f_list->first);
  for (i = 1; (MARK(4, 5), f_ele) && ((mark(4, 4), i < n)); (mark(4, 2), i++)) {
    (mark(4, 3), f_ele = f_ele->next);
  }
  return (MARK(4, 1), f_ele);
}

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

/*-----------------------------------------------------------------------------
   free_ele
       deallocate the ptr. Caution: The ptr should point to an object
       allocated in a single call to malloc.
-----------------------------------------------------------------------------*/
void free_ele(Ele *ptr) {
  (MARK(6, 1), free(ptr));
  MARK(6, 13);
  return;
}

int alloc_proc_num;
int num_processes;
Ele *cur_proc;
List *prio_queue[MAXPRIO + 1]; /* 0th element unused */
List *block_queue;

void finish_process(void) {
  (MARK(7, 3), schedule());
  if (cur_proc) {
    (mark(7, 2), fprintf(stdout, "%d ", cur_proc->val));
    free_ele(cur_proc);
    num_processes--;
  }
  MARK(7, 1);
  return;
}

void finish_all_processes(void) {
  MARK(8, 5);
  int i;
  int total;
  total = num_processes;
  for (i = 0; (MARK(8, 4), i < total); (mark(8, 2), i++)) {
    (mark(8, 3), finish_process());
  }
  MARK(8, 1);
  return;
}

void schedule(void) {
  MARK(9, 6);
  int i;

  cur_proc = NULL;
  for (i = MAXPRIO; (MARK(9, 5), i > 0); (mark(9, 2), i--)) {
    if ((mark(9, 4), prio_queue[i]->mem_count > 0)) {
      cur_proc = prio_queue[i]->first;
      prio_queue[i] = del_ele(prio_queue[i], cur_proc);
      MARK(9, 3);
      return;
    }
  }
  MARK(9, 1);
  return;
}

void upgrade_process_prio(int prio, short numerator) {
  MARK(10, 6);
  int count;
  int n;
  Ele *proc;
  List *src_queue, *dest_queue;

  if (prio >= MAXPRIO) {
    MARK(10, 5);
    return;
  }
  (mark(10, 4), src_queue = prio_queue[prio]);
  dest_queue = prio_queue[prio + 1];
  count = src_queue->mem_count;

  if (count > 0) {
    (mark(10, 3), n = (int)(((count * numerator) / RATIO_QUANTA) + 1));
    proc = find_nth(src_queue, n);
    if (proc) {
      src_queue = (mark(10, 2), del_ele(src_queue, proc));
      /* append to appropriate prio queue */
      proc->priority = prio;
      dest_queue = append_ele(dest_queue, proc);
    }
  }
  MARK(10, 1);
  return;
}

void unblock_process(short numerator) {
  MARK(11, 4);
  int count;
  int n;
  Ele *proc;
  int prio;
  if (block_queue) {
    (mark(11, 3), count = block_queue->mem_count);
    n = (int)(((count * numerator) / RATIO_QUANTA) + 1);
    proc = find_nth(block_queue, n);
    if (proc) {
      block_queue = (mark(11, 2), del_ele(block_queue, proc));
      /* append to appropriate prio queue */
      prio = proc->priority;
      prio_queue[prio] = append_ele(prio_queue[prio], proc);
    }
  }
  MARK(11, 1);
  return;
}

void quantum_expire(void) {
  MARK(12, 3);
  int prio;
  schedule();
  if (cur_proc) {
    (mark(12, 2), prio = cur_proc->priority);
    prio_queue[prio] = append_ele(prio_queue[prio], cur_proc);
  }
  MARK(12, 1);
  return;
}

void block_process(void) {
  (MARK(13, 3), schedule());
  if (cur_proc) {
    block_queue = (mark(13, 2), append_ele(block_queue, cur_proc));
  }
  MARK(13, 1);
  return;
}

Ele *new_process(int prio) {
  MARK(14, 1);
  Ele *proc;
  proc = new_ele(alloc_proc_num++);
  proc->priority = prio;
  num_processes++;
  return (MARK(14, 13), proc);
}

void add_process(int prio) {
  MARK(15, 1);
  Ele *proc;
  proc = new_process(prio);
  prio_queue[prio] = append_ele(prio_queue[prio], proc);
  MARK(15, 13);
  return;
}

void init_prio_queue(int prio, int num_proc) {
  MARK(16, 5);
  List *queue;
  Ele *proc;
  int i;

  queue = new_list();
  for (i = 0; (MARK(16, 4), i < num_proc); (mark(16, 2), i++)) {
    proc = (mark(16, 3), new_process(prio));
    queue = append_ele(queue, proc);
  }
  prio_queue[prio] = queue;
  MARK(16, 1);
  return;
}

void initialize(void) {
  (MARK(17, 1), alloc_proc_num = 0);
  num_processes = 0;
  MARK(17, 13);
  return;
}

/* test driver */
int main(int argc, char *argv[]) {
  MARK(18, 27);
  int command;
  int prio;
  short numerator;
  int status;

  if (argc < (MAXPRIO + 1)) {
    fprintf(stdout, "incorrect usage\n");
    return (MARK(18, 26), 1);
  }

  (mark(18, 25), initialize());
  for (prio = MAXPRIO; (MARK(18, 24), prio >= 1); (mark(18, 22), prio--)) {
    init_prio_queue(prio, (mark(18, 23), atoi(argv[prio])));
  }
  for (status = (mark(18, 21), fscanf(stdin, "%d", &command));
       (((MARK(18, 20), status != EOF)) && (mark(18, 19), status));
       status = (mark(18, 2), fscanf(stdin, "%d", &command))) {
    switch ((mark(18, 3), command)) {
    case FINISH:
      (mark(18, 18), finish_process());
      break;
    case BLOCK:
      (mark(18, 17), block_process());
      break;
    case QUANTUM_EXPIRE:
      (mark(18, 16), quantum_expire());
      break;
    case UNBLOCK:
      (mark(18, 15), fscanf(stdin, "%hd", &numerator));
      unblock_process(numerator);
      break;
    case UPGRADE_PRIO:
      (mark(18, 14), fscanf(stdin, "%d", &prio));
      fscanf(stdin, "%hd", &numerator);
      if (prio > MAXPRIO || (mark(18, 13), prio <= 0)) {
        fprintf(stdout, "** invalid priority\n");
        return (MARK(18, 12), 1);
      } else {
        (mark(18, 11), upgrade_process_prio(prio, numerator));
      }
      break;
    case NEW_JOB:
      (mark(18, 9), fscanf(stdin, "%d", &prio));
      if (prio > MAXPRIO || (mark(18, 8), prio <= 0)) {
        fprintf(stdout, "** invalid priority\n");
        return (MARK(18, 7), 1);
      } else {
        (mark(18, 6), add_process(prio));
      }
      break;
    case FLUSH:
      (mark(18, 4), finish_all_processes());
      break;
    }
  }
  return (MARK(18, 1), 0);
}

/* A simple input spec:

  a.out n3 n2 n1

  where n3, n2, n1 are non-negative integers indicating the number of
  initial processes at priority 3, 2, and 1, respectively.

  The input file is a list of commands of the following kinds:
   (For simplicity, comamnd names are integers (NOT strings)

  FINISH            ;; this exits the current process (printing its number)
  NEW_JOB priority  ;; this adds a new process at specified priority
  BLOCK             ;; this adds the current process to the blocked queue
  QUANTUM_EXPIRE    ;; this puts the current process at the end
                    ;;      of its prioqueue
  UNBLOCK ratio     ;; this unblocks a process from the blocked queue
                    ;;     and ratio is used to determine which one

  UPGRADE_PRIO small-priority ratio ;; this promotes a process from
                    ;; the small-priority queue to the next higher priority
                    ;;     and ratio is used to determine which process

  FLUSH             ;; causes all the processes from the prio queues to
                    ;;    exit the system in their priority order

where
 NEW_JOB        1
 UPGRADE_PRIO   2
 BLOCK          3
 UNBLOCK        4
 QUANTUM_EXPIRE 5
 FINISH         6
 FLUSH          7
and priority is in        1..3
and small-priority is in  1..2
and ratio is in           0.0..1.0

 The output is a list of numbers indicating the order in which
 processes exit from the system.

*/

