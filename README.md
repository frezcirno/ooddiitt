#How to build lcl-klee

This is a collection of our notes about the installation of [KLEE](https://klee.github.io/). This document contains a step by step recipe for building lcl-klee and its dependencies.

----------

##Introduction

###The resulting directory structure:
```
klee
├── org-klee
├── lcl-klee
├── klee-uclibc (linux only)
├── llvm-3.4
├── minisat
├── stp
└── z3
```

##Usefull Links:

* [The official (but buggy) installation manual](https://klee.github.io/build-llvm34/)
* [Build LLVM on your own](http://www.llvm.org/docs/GettingStarted.html#getting-started-quickly-a-summary)
* [The old official installation manual](https://llvm.org/svn/llvm-project/klee/trunk/www/GetStarted.html?p=156062)
* [More recent user installation for Ubuntu 14.04 LTS](http://blog.opensecurityresearch.com/2014/07/klee-on-ubuntu-1404-lts-64bit.html)
* [STP installation manual with build options](https://github.com/stp/stp/blob/master/INSTALL.md)
* [metaSMT-Support for KLEE](http://srg.doc.ic.ac.uk/projects/klee-multisolver/getting-started.html)

##Fedora (with stow)

###Notes:  

some areas to update: need 32bit dev libraries, curses, run ldconfig after installing new dynamic libs. 
On fedora 27, some libs installed to lib64.  not found by ld. add to /etc/ld.so.conf.d

###Step 1: Install required tools for the build

~~~
Packages to install:
bison cmake curl flex git boost-devel perftools-devel ninja-build graphviz doxygen

Set the install path:
export KLEE_DIR=/usr/local/stow/lcl-klee
~~~

###Step 2: LLVM

+-------------+---------------------------------------------------------+-------------------------------+
| Source      | URL                                                     | Directory                     |
+=============+=========================================================+===============================+
| llvm        | http://releases.llvm.org/3.4.2/llvm-3.4.2.src.tar.gz    | llvm-3.4                      |
+-------------+---------------------------------------------------------+-------------------------------+
| clang       | http://releases.llvm.org/3.4.2/cfe-3.4.2.src.tar.gz     | llvm-3.4/tools/clang          |
+-------------+---------------------------------------------------------+-------------------------------+

edit include/llvm/Support/CommandLine.h:1654 to correct erroneous indention

```
cd llvm-3.4
mkdir cmake-build-release
cd cmake-build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE='Release' \
 -DCMAKE_INSTALL_PREFIX="${KLEE_DIR}" \
 -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
 -DCMAKE_CXX_FLAGS="-Wimplicit-fallthrough=0 -Wno-unused-function -Wno-unused-local-typedefs -Wno-misleading-indentation" \
 -DCMAKE_C_FLAGS="-Wimplicit-fallthrough=0 -Wno-unused-function -Wno-unused-local-typedefs -Wno-misleading-indentation" \
 -DLLVM_TARGETS_TO_BUILD='host' \
 ..

ninja
ninja install
cd ..\..
```

###Step 3: Minisat

```
git clone https://github.com/stp/minisat.git
cd minisat
mkdir cmake-build-release
cd cmake-build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE='Release' \
 -DCMAKE_INSTALL_PREFIX=${KLEE_DIR} \
 ..

ninja
ninja install
cd ..\..
```

###Step 4: STP

```
git clone https://github.com/stp/stp.git
cd stp
mkdir cmake-build-release
cd cmake-build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE="Release" \
 -DCMAKE_INSTALL_PREFIX=${KLEE_DIR} \
 -DENABLE_PYTHON_INTERFACE:BOOL=OFF \
 -DTUNE_NATIVE:BOOL=ON \
 ..

ninja
ninja install
cd ../..
```

###Step 5: Z3

```
git clone https://github.com/Z3Prover/z3.git
cd z3
mkdir cmake-build-release
cd cmake-build-release

cmake -G Ninja \
 -DCMAKE_BUILD_TYPE="Release" \
 -DCMAKE_INSTALL_PREFIX=${KLEE_DIR} \
 ..

ninja
ninja install
cd ../..
```

Installation places a new shared object library in /usr/local/lib. Need to run `sudo ldconfig` so the os can find it.

###Step 6: uclibc and the POSIX environment model

```
git clone https://github.com/klee/klee-uclibc.git
cd klee-uclibc
./configure --make-llvm-lib --with-llvm-config=${KLEE_DIR}/bin/llvm-config
make -j `nproc`
cd ..
```

###Step 7: org-klee

Original klee code for reference. Not required to build.

```
git clone https://github.com/klee/klee.git org-klee
```

###Step 8: lcl-klee

```
git clone https://github.gatech.edu/arktos/lcl-klee.git
cd lcl-klee
mkdir cmake-build-release
cd cmake-build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE='Release' \
 -DCMAKE_INSTALL_PREFIX=${KLEE_DIR} \
 -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
 -DCMAKE_CXX_FLAGS="-fno-rtti" \
 -DUSE_CXX11=ON \
 -DENABLE_TCMALLOC=ON \
 -DENABLE_SOLVER_STP=ON \
 -DENABLE_SOLVER_Z3=ON \
 -DENABLE_POSIX_RUNTIME=ON \
 -DENABLE_KLEE_UCLIBC=ON \
 -DKLEE_UCLIBC_PATH="../../klee-uclibc" \
 -DENABLE_UNIT_TESTS=OFF \
 -DENABLE_SYSTEM_TESTS=OFF \
 -DLLVM_CONFIG_BINARY="${KLEE_DIR}/bin/llvm-config" \
 ..

```

Final installed build in /usr/local/stow/lcl-klee. Activate by `sudo stow --dir=/usr/local/stow lcl-klee`

-----------

##MacOS (with homebrew)

###Step 1: Install required tools for the build

~~~
Packages to install (via home brew):
boost cmake ninja gperftools graphviz doxygen

Set the install path:
export KLEE_DIR=$(brew --prefix)/Cellar/klee/1.3.0
~~~

###Step 2: LLVM

+-------------+---------------------------------------------------------+-------------------------------+
| Source      | URL                                                     | Directory                     |
+=============+=========================================================+===============================+
| llvm        | http://releases.llvm.org/3.4.2/llvm-3.4.2.src.tar.gz    | llvm-3.4                      |
+-------------+---------------------------------------------------------+-------------------------------+
| clang       | http://releases.llvm.org/3.4.2/cfe-3.4.2.src.tar.gz     | llvm-3.4/tools/clang          |
+-------------+---------------------------------------------------------+-------------------------------+

```
cd llvm-3.4
mkdir cmake-build-release
cd cmake-build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE='Release' \
 -DCMAKE_INSTALL_PREFIX="${KLEE_DIR}" \
 -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
 -DLLVM_TARGETS_TO_BUILD='host' \
 ..

ninja
ninja install
cd ..\..
```

###Step 3: Minisat

```
git clone https://github.com/stp/minisat.git
cd minisat
mkdir cmake-build-release
cd cmake-build-release
cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE='Release' \
 -DCMAKE_INSTALL_PREFIX=${KLEE_DIR} \
 ..

ninja
ninja install
cd ..\..
```

###Step 4: STP

```
git clone https://github.com/stp/stp.git
cd stp
mkdir cmake-build-release
cd cmake-build-release
cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE="Release" \
 -DCMAKE_INSTALL_PREFIX=${KLEE_DIR} \
 -DENABLE_PYTHON_INTERFACE:BOOL=OFF \
 -DTUNE_NATIVE:BOOL=ON \
 ..

ninja
ninja install
cd ../..
```

###Step 5: Z3

```
git clone https://github.com/Z3Prover/z3.git
cd z3
mkdir cmake-build-release
cd cmake-build-release
cmake -G Ninja \
 -DCMAKE_BUILD_TYPE="Release" \
 -DCMAKE_INSTALL_PREFIX=${KLEE_DIR} \
 ..

ninja
ninja install
cd ../..

```

###Step 6: org-klee

```
git clone https://github.com/klee/klee.git org-klee
```

###Step 7: lcl-klee

```
git clone https://github.gatech.edu/arktos/lcl-klee.git
cd lcl-klee
mkdir cmake-build-release
cd cmake-build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE='Release' \
 -DCMAKE_INSTALL_PREFIX=${KLEE_DIR} \
 -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
 -DCMAKE_CXX_FLAGS="-fno-rtti" \
 -DCMAKE_EXE_LINKER_FLAGS="-pagezero_size 0x1000" \
 -DUSE_CXX11=ON \
 -DENABLE_TCMALLOC=ON \
 -DENABLE_SOLVER_STP=ON \
 -DENABLE_SOLVER_Z3=ON \
 -DENABLE_UNIT_TESTS=OFF \
 -DENABLE_SYSTEM_TESTS=OFF \
 -DLLVM_CONFIG_BINARY="${KLEE_DIR}/bin/llvm-config" \
 ..

ninja
ninja install
cd ../..
```

Final installed build in /usr/local/Cellar/klee/1.3.0. Activate by `brew link klee`
