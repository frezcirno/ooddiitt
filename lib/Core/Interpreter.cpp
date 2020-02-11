//===-- Interpreter.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <llvm/Support/Path.h>
#include <llvm/Support/Debug.h>
#include <klee/Internal/Support/Debug.h>
#include "klee/Interpreter.h"

using namespace llvm;
using namespace std;

namespace klee {


InterpreterHandler::InterpreterHandler(const std::string &od, const std::string &_md_name) :
    interpreter(nullptr), outputDirectory(od), output_created(false) {

  file_name = _md_name;
  module_name = boost::filesystem::path(_md_name).stem().string();

  if (!outputDirectory.empty()) {
    boost::system::error_code ec;
    // create the output directory if not already exists
    if (!boost::filesystem::exists(outputDirectory)) {
      boost::filesystem::create_directories(outputDirectory, ec);
      output_created = true;
    }
  }
}

InterpreterHandler::InterpreterHandler(const std::string &od, const std::string &_md_name, const std::string &_prefix) :
  InterpreterHandler(od, _md_name) { prefix = _prefix; }

std::string InterpreterHandler::getTestFilename(const std::string &ext, unsigned id) {
  std::ostringstream filename;
  filename << prefix << std::setfill('0') << std::setw(10) << id << '.' << ext;
  return filename.str();
}

std::string InterpreterHandler::getOutputFilename(const std::string &filename) {
  boost::filesystem::path file = outputDirectory;
  file /= filename;
  return file.string();
}

llvm::raw_fd_ostream *InterpreterHandler::openOutputFile(const std::string &filename, bool overwrite) {

  std::string Error;
  std::string path = getOutputFilename(filename);
  llvm::sys::fs::OpenFlags fs_options = llvm::sys::fs::F_Binary;
  if (overwrite) { fs_options |= llvm::sys::fs::F_Excl; }
  auto *result = new llvm::raw_fd_ostream(path.c_str(), Error, fs_options);
  if (!Error.empty()) {
    if (!boost::algorithm::ends_with(Error, "File exists")) {
      klee_warning("error opening file \"%s\".  KLEE may have run out of file "
                   "descriptors: try to increase the maximum number of open file "
                   "descriptors by using ulimit (%s).",
                   filename.c_str(), Error.c_str());
    }
    delete result;
    result = nullptr;
  }
  return result;
}

bool InterpreterHandler::openTestCaseFile(std::ofstream &fout, unsigned test_id, string &name) {

  assert(!fout.is_open());
  assert(!prefix.empty());
  name = getTestFilename("json", test_id);
  string pathname = getOutputFilename(name);
  fout.open(pathname);
  return fout.is_open();
}

string InterpreterHandler::getRunTimeLibraryPath(const char *argv0) {

  // allow specifying the path to the runtime library
  const char *env = getenv("KLEE_RUNTIME_LIBRARY_PATH");
  if (env) {
    return string(env);
  }

  if (strlen(KLEE_INSTALL_RUNTIME_DIR) > 0) {
    return string(KLEE_INSTALL_RUNTIME_DIR);
  }

  // Take any function from the execution binary but not main (as not allowed by
  // C++ standard)
  void *MainExecAddr = (void *)(intptr_t)getRunTimeLibraryPath;
  SmallString<128> toolRoot(llvm::sys::fs::getMainExecutable(argv0, MainExecAddr));

  // Strip off executable so we have a directory path
  llvm::sys::path::remove_filename(toolRoot);
  SmallString<128> libDir;

  if (strlen( KLEE_INSTALL_BIN_DIR ) != 0 &&
      strlen( KLEE_INSTALL_RUNTIME_DIR ) != 0 &&
      toolRoot.str().endswith( KLEE_INSTALL_BIN_DIR ))  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() << "Using installed KLEE library runtime: ");
    libDir = toolRoot.str().substr(0,toolRoot.str().size() - strlen( KLEE_INSTALL_BIN_DIR ));
    llvm::sys::path::append(libDir, KLEE_INSTALL_RUNTIME_DIR);
  } else {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() << "Using build directory KLEE library runtime :");
    libDir = KLEE_DIR;
    llvm::sys::path::append(libDir,RUNTIME_CONFIGURATION);
    llvm::sys::path::append(libDir,"lib");
  }

  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() << libDir.c_str() << "\n");
  return libDir.str();
}

}; // end klee namespace
