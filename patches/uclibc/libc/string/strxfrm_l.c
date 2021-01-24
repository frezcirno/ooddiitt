/*
 * Copyright (C) 2000-2005 Erik Andersen <andersen@uclibc.org>
 *
 * Licensed under the LGPL v2.1, see the file COPYING.LIB in this tarball.
 */

#define WANT_WIDE
#define __UCLIBC_DO_XLOCALE
#define L_strxfrm_l
#define __init_collate_state __init_collate_state_str_l
#define __collate_next_weight __collate_next_weight_str_l
#define __collate_lookup __collate_lookup_str_l
#include "_collate.c"
