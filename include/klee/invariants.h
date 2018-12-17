
#ifndef __INVARIANTS_H__
#define __INVARIANTS_H__

#include "stdint.h"
#include "stddef.h"

#define INVARIANT(a)        pgklee_hard_assume(a)
#define EXPECT(a)           pgklee_soft_assume(a)
#define IMPLIES(a, b)       pgklee_implies(a, b)
#define HOLDS(a)            pgklee_expr_holds(a)
#define MAY_HOLD(a)         pgklee_expr_mayhold(a)
#define VALID_POINTER(p)    pgklee_valid_ptr(p)
#define OBJECT_SIZE(p)      pgklee_object_size(p)

void pgklee_hard_assume(uintptr_t condition);
void pgklee_soft_assume(uintptr_t condition);
void pgklee_implies(uintptr_t a, uintptr_t b);
int pgklee_expr_holds(uintptr_t condition);
int pgklee_expr_mayhold(uintptr_t condition);
int pkgklee_valid_ptr(void *ptr);
unsigned pgklee_object_size(void *ptr);

#endif /* __INVARIANTS_H__ */
