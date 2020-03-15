//===-- ErrorHandling.cpp -------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Internal/Support/ErrorHandling.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include <boost/filesystem.hpp>

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <assert.h>
#include <string.h>

#include <set>

using namespace klee;
using namespace llvm;

static const char *warningPrefix = "WARNING";
static const char *warningOncePrefix = "WARNING ONCE";
static const char *errorPrefix = "ERROR";
static const char *infoPrefix = "INFO";

namespace {
cl::opt<bool> Silent("silent", cl::init(false), cl::desc("send warning and info messages to stderr instead of stdout"));
}

static void klee_vfmessage(FILE *fp, const char *pfx, const char *msg, va_list ap) {
  fprintf(fp, "%s: ", pfx);
  vfprintf(fp, msg, ap);
  putc('\n', fp);
}

void klee::klee_error(const char *msg, ...) {
  va_list ap;
  va_start(ap, msg);
  klee_vfmessage(stderr, errorPrefix, msg, ap);
  va_end(ap);
  exit(2);
}

void klee::klee_warning(const char *msg, ...) {
  va_list ap;
  va_start(ap, msg);
  klee_vfmessage(Silent ? stderr : stdout, warningPrefix, msg, ap);
  va_end(ap);
}

/* Prints a warning once per message. */
void klee::klee_warning_once(const void *id, const char *msg, ...) {
  static std::set<std::pair<const void *, const char *> > keys;

  std::pair<const void *, const char *> key;

  /* "calling external" messages contain the actual arguments with
     which we called the external function, so we need to ignore them
     when computing the key. */
  if (strncmp(msg, "calling external", strlen("calling external")) != 0)
    key = std::make_pair(id, msg);
  else
    key = std::make_pair(id, "calling external");

  if (!keys.count(key)) {
    keys.insert(key);
    va_list ap;
    va_start(ap, msg);
    klee_vfmessage(Silent ? stderr : stdout, warningOncePrefix, msg, ap);
    va_end(ap);
  }
}

void klee::klee_message(const char *msg, ...) {
  va_list ap;
  va_start(ap, msg);
  klee_vfmessage(Silent ? stderr : stdout, infoPrefix, msg, ap);
  va_end(ap);
}

