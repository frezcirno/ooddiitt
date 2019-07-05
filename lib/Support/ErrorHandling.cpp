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
static const char *notePrefix = "NOTE";

static std::string output_dir;
static std::string output_prefix;
static FILE* message_file = NULL;
static FILE* warning_file = NULL;
static bool initialized = false;

namespace {
cl::opt<bool> WarningsOnlyToFile(
    "warnings-only-to-file", cl::init(false),
    cl::desc("All warnings will be written to warnings.txt only.  If disabled, "
             "they are also written on screen."));
}

static bool shouldSetColor(const char *pfx, const char *msg,
                           const char *prefixToSearchFor) {
  if (pfx && strcmp(pfx, prefixToSearchFor) == 0)
    return true;

  if (llvm::StringRef(msg).startswith(prefixToSearchFor))
    return true;

  return false;
}

static void klee_vfmessage(FILE *fp, const char *pfx, const char *msg,
                           va_list ap) {
  if (!fp)
    return;

  llvm::raw_fd_ostream fdos(fileno(fp), /*shouldClose=*/false,
                            /*unbuffered=*/true);
  bool modifyConsoleColor = fdos.is_displayed() && (fp == stderr);

  if (modifyConsoleColor) {

    // Warnings
    if (shouldSetColor(pfx, msg, warningPrefix))
      fdos.changeColor(llvm::raw_ostream::MAGENTA,
                       /*bold=*/false,
                       /*bg=*/false);

    // Once warning
    if (shouldSetColor(pfx, msg, warningOncePrefix))
      fdos.changeColor(llvm::raw_ostream::MAGENTA,
                       /*bold=*/true,
                       /*bg=*/false);

    // Errors
    if (shouldSetColor(pfx, msg, errorPrefix))
      fdos.changeColor(llvm::raw_ostream::RED,
                       /*bold=*/true,
                       /*bg=*/false);

    // Notes
    if (shouldSetColor(pfx, msg, notePrefix))
      fdos.changeColor(llvm::raw_ostream::WHITE,
                       /*bold=*/true,
                       /*bg=*/false);
  }

  fdos << "KLEE: ";
  if (pfx)
    fdos << pfx << ": ";

  // FIXME: Can't use fdos here because we need to print
  // a variable number of arguments and do substitution
  vfprintf(fp, msg, ap);
  fflush(fp);

  fdos << "\n";

  if (modifyConsoleColor)
    fdos.resetColor();

  fdos.flush();
}

void klee::init_error_handling(const char *dir, const char *prefix) {

  output_dir = dir;
  output_prefix = prefix;
  initialized = true;
}

void klee::term_error_handling() {

  if (message_file != NULL) {
    fclose(message_file);
    message_file = NULL;
  }
  if (warning_file != NULL) {
    fclose(warning_file);
    warning_file = NULL;
  }
}

FILE *get_message_file() {

  if (message_file == nullptr) {
    if (!initialized) klee_error("message log not initialized");
    std::string filename = "messages.txt";
    if (!output_prefix.empty()) {
      filename = output_prefix + '-' + filename;
    }
    boost::filesystem::path path(output_dir);
    path.append(filename);
    if ((message_file = fopen(path.c_str(), "w")) == nullptr)
      klee_error("cannot open file \"%s\": %s", path.c_str(), strerror(errno));
  }
  return message_file;
}

FILE *get_warning_file() {

  if (warning_file == nullptr) {
    if (!initialized) klee_error("warning log not initialized");
    std::string filename = "warnings.txt";
    if (!output_prefix.empty()) {
      filename = output_prefix + '-' + filename;
    }
    boost::filesystem::path path(output_dir);
    path.append(filename);
    if ((warning_file = fopen(path.c_str(), "w")) == nullptr)
      klee_error("cannot open file \"%s\": %s", path.c_str(), strerror(errno));
  }
  return warning_file;
}

void klee::klee_message(const char *msg, ...) {
  va_list ap;
  va_start(ap, msg);
  klee_vfmessage(get_message_file(), NULL, msg, ap);
  va_end(ap);
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
  klee_vfmessage(get_warning_file(), warningPrefix, msg, ap);
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
    klee_vfmessage(get_warning_file(), warningOncePrefix, msg, ap);
    va_end(ap);
  }
}
