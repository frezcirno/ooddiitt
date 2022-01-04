# How to build brt-klee

This is a collection of our notes about the installation of [KLEE](https://klee.github.io/). This document contains a step by step recipe for building brt-klee and its dependencies.

----------

## Introduction

### The resulting directory structure:
```
pse-tools
├── klee (optional)
├── brt-klee
├── klee-uclibc
├── llvm-3.4
├── minisat
├── stp
└── z3
```

## Usefull Links:

* [The official installation manual](https://klee.github.io/build-llvm34/)
* [Build LLVM on your own](http://www.llvm.org/docs/GettingStarted.html#getting-started-quickly-a-summary)
* [The old official installation manual](https://llvm.org/svn/llvm-project/klee/trunk/www/GetStarted.html?p=156062)
* [More recent user installation for Ubuntu 14.04 LTS](http://blog.opensecurityresearch.com/2014/07/klee-on-ubuntu-1404-lts-64bit.html)
* [STP installation manual with build options](https://github.com/stp/stp/blob/master/INSTALL.md)
* [metaSMT-Support for KLEE](http://srg.doc.ic.ac.uk/projects/klee-multisolver/getting-started.html)

## Ubuntu (with stow)

### Notes:

some areas to update: need 32bit dev libraries, curses, run ldconfig after installing new dynamic libs.
On fedora 27, some libs installed to lib64.  not found by ld. add to /etc/ld.so.conf.d

### Step 1: Install required tools for the build

~~~
Packages to install:
bison cmake curl flex git libtcmalloc-minimal4 libgoogle-perftools-dev ninja-build libncurses5-dev stow


INSTALL_BASE=/usr/local/stow
~~~

### Step 2: LLVM

Install as per `https://github.gatech.edu/arktos/llvm-3.4.git`

### Step 3: Minisat

```
git clone https://github.com/stp/minisat.git
cd minisat
mkdir build-release
cd build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE=Release \
 -DSTATIC_BINARIES=ON \
 -DBUILD_SHARED_LIBS=OFF \
 -DCMAKE_INSTALL_PREFIX="$INSTALL_BASE/stp" \
 ..

ninja
ninja install
cd ..\..
```

### Step 4: STP

```
git clone https://github.com/stp/stp.git
cd stp
git checkout tags/2.1.2
mkdir build-release
cd build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE=Release \
 -DCMAKE_INSTALL_PREFIX="$INSTALL_BASE/stp" \
 -DMINISAT_INCLUDE_DIRS="$INSTALL_BASE/stp/include" \
 -DMINISAT_LIBDIR="$INSTALL_BASE/stp/lib" \
 -DENABLE_PYTHON_INTERFACE:BOOL=OFF \
 -DBUILD_SHARED_LIBS=OFF \
 -DTUNE_NATIVE:BOOL=ON \
 -DNO_BOOST=ON \
 ..

ninja
ninja install
cd ../..

sudo stow --dir=/usr/local/stow stp
```

### Step 5: Z3

```
git clone https://github.com/Z3Prover/z3.git
cd z3
git checkout z3-4.8.12
mkdir build-release
cd build-release

cmake -G Ninja \
 -DCMAKE_BUILD_TYPE=Release \
 -DCMAKE_INSTALL_PREFIX="$INSTALL_BASE/z3" \
 ..

ninja
ninja install
cd ../..

sudo stow --dir=/usr/local/stow z3
```

Installation places a new shared object library in /usr/local/lib. Need to run `sudo ldconfig` so the os can find it.

### Step 6: uclibc and the POSIX environment model

```
git clone https://github.com/klee/klee-uclibc.git
cd klee-uclibc

copy patches from brt-klee

./configure --make-llvm-lib --with-llvm-config="${INSTALL_BASE}/llvm-3.4/bin/llvm-config"
make KLEE_CFLAGS="-DKLEE_SYM_PRINTF" -j `nproc`
cd ..
```

### Step 7: klee (OPTIONAL)

```
git clone https://github.com/klee/klee.git
cd klee
mkdir build-release
cd build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE=Release \
 -DCMAKE_INSTALL_PREFIX="$INSTALL_BASE/klee" \
 -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
 -DCMAKE_CXX_FLAGS="-fno-rtti" \
 -DENABLE_TCMALLOC=ON \
 -DENABLE_SOLVER_STP=ON \
 -DENABLE_SOLVER_Z3=ON \
 -DENABLE_POSIX_RUNTIME=ON \
 -DENABLE_KLEE_UCLIBC=ON \
 -DKLEE_UCLIBC_PATH="../../klee-uclibc" \
 -DENABLE_UNIT_TESTS=OFF \
 -DENABLE_SYSTEM_TESTS=OFF \
 -DLLVM_CONFIG_BINARY="$INSTALL_BASE/llvm-3.4/bin/llvm-config" \
 ..

sudo stow --dir=/usr/local/stow klee
```

### Step 8: brt-klee

```
git clone https://github.gatech.edu/arktos/brt-klee.git
cd brt-klee
mkdir build-release
cd build-release

cmake -G "Ninja" \
 -DCMAKE_BUILD_TYPE=Release \
 -DCMAKE_INSTALL_PREFIX="$INSTALL_BASE/pse-tools" \
 -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
 -DCMAKE_CXX_FLAGS="-fno-rtti -Wno-class-memaccess -Wno-deprecated-copy -Wno-unused-variable -Wno-unused-but-set-variable" \
 -DENABLE_TCMALLOC=ON \
 -DENABLE_KLEE_ASSERTS=ON \
 -DENABLE_SOLVER_STP=ON \
 -DENABLE_SOLVER_Z3=ON \
 -DENABLE_POSIX_RUNTIME=OFF \
 -DENABLE_UNIT_TESTS=OFF \
 -DENABLE_SYSTEM_TESTS=OFF \
 -DENABLE_KLEE_UCLIBC=ON \
 -DKLEE_UCLIBC_PATH="../../klee-uclibc" \
 -DUSE_CXX11=ON \
 -DLLVM_CONFIG_BINARY="$INSTALL_BASE/llvm-3.4/bin/llvm-config" \
 ..

ninja
ninja install

sudo stow --dir=/usr/local/stow pse-tools
```

Run `ldconfig` to update shared library cache


