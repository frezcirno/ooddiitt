
#ifndef __INVARIANTS_H__
#define __INVARIANTS_H__

#define INVARIANT(a)        pgklee_hard_assume(a)
#define EXPECT(a)           pgklee_soft_assume(a)
#define IMPLIES(a, b)       pgklee_hard_assume( (~(a)) || (b) )
#define HOLDS(a)            pgklee_expr_holds(a)
#define MAY_HOLD(a)         pgklee_expr_may_hold(a)
#define VALID_POINTER(p)    pgklee_valid_ptr(p)
#define OBJECT_SIZE(p)      pgklee_object_size(p)

#endif /* __INVARIANTS_H__ */
