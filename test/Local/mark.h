#ifndef MARK_INCLUDED
#define MARK_INCLUDED

#include <setjmp.h>

/* the replay code expects the target to define these functions in mark.c: */
void init_markers(void);
void term_markers(void);
void init_trace(const char *trace_name);
void term_trace(void);

/* the target expects the generated replay code to implement these functions in <frag>/<frag>.c: */
//int run_test(unsigned int counter);

// the other header files in include/ need to be included when run on
// the target device, however mark() implementation needs to be
// different on the target (and defined by macro to completely disable
// it for some configurations).
// mark() and MARK() implementation varies depending on signal measurement

#define MARK_TYPE_NONE     0
#define MARK_TYPE_TIME     1
#define MARK_TYPE_ALL      2
#define MARK_TYPE_REPLAY   3
// defined on the command line (values below are valid): (by default MARK_TYPE_REPLAY)
#ifndef MARK_TYPE
#define MARK_TYPE          MARK_TYPE_REPLAY
#endif

#if MARK_TYPE == MARK_TYPE_REPLAY
void mark(int fnID, int mkID);
void MARK(int fnID, int mkID);
#else
// FIXME: workaround for nios, this doesn't belong here
typedef jmp_buf sigjmp_buf;
#endif

#if MARK_TYPE == MARK_TYPE_TIME
#define mark(func, num) (void) NULL
#define MARK(func, num) eminst_mark_time()
#define mark_4th(func, num, val) {if (((val)&0x3) == 0) mark(func, num);}
/* the target expects the generated replay code to implement these functions in <frag>/<frag>.c: */
int run_test(unsigned int counter);
extern sigjmp_buf point; // this is defined in <frag>/<frag>.c but used when run_test is called
#endif

#if MARK_TYPE == MARK_TYPE_ALL
#define mark(func, num) eminst_mark(100000+func*1000+num)
#define MARK(func, num) eminst_mark(func*1000+num)
#define mark_4th(func, num, val) (((val)&0x3) == 0) ? mark(func, num), 0 : 0
/* the target expects the generated replay code to implement these functions in <frag>/<frag>.c: */
int run_test(unsigned int counter);
extern sigjmp_buf point; // this is defined in <frag>/<frag>.c but used when run_test is called
#endif

#if MARK_TYPE == MARK_TYPE_NONE
#define mark(func, num) (void) NULL
#define MARK(func, num) (void) NULL
#define mark_4th(func, num, val) (void) NULL
/* the target expects the generated replay code to implement these functions in <frag>/<frag>.c: */
int run_test(unsigned int counter);
extern sigjmp_buf point; // this is defined in <frag>/<frag>.c but used when run_test is called
#endif

// FIXME: this doesn't belong here
#define MARK_ONCHIP_MEM    0
#if MARK_ONCHIP_MEM
void eminst_mark_time(void) __attribute__((section (".tightly_coupled_inst_memory")));
void eminst_mark(int num) __attribute__((section (".tightly_coupled_inst_memory")));
#else
void eminst_mark_time(void);
void eminst_mark(int num);
#endif

#endif // MARK_INCLUDED

