//===-- ErrorHandling.h -----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef __KLEE_ERROR_HANDLING_H__
#define __KLEE_ERROR_HANDLING_H__

#ifdef __CYGWIN__
#ifndef WINDOWS
#define WINDOWS
#endif
#endif

#include <stdio.h>

namespace klee {

/// Print "ERROR: " followed by the msg in printf format and a
/// newline on stderr and to warnings.txt, then exit with an error.
void klee_error(const char *msg, ...) __attribute__((format(printf, 1, 2), noreturn));

/// Print "INFO: " followed by the msg in printf format and a
/// newline on stderr and to messages.txt.
void klee_message(const char *msg, ...) __attribute__((format(printf, 1, 2)));

/// Print "WARNING: " followed by the msg in printf format and a
/// newline on stderr and to warnings.txt.
void klee_warning(const char *msg, ...) __attribute__((format(printf, 1, 2)));

/// Print "WARNING: " followed by the msg in printf format and a
/// newline on stderr and to warnings.txt. However, the warning is only
/// printed once for each unique (id, msg) pair (as pointers).
void klee_warning_once(const void *id, const char *msg, ...) __attribute__((format(printf, 2, 3)));
}

#endif /* __KLEE_ERROR_HANDLING_H__ */
