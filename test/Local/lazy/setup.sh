
rm -rf *.bc brt-out-tmp

IGEN_FLAGS="-progression=g:300"

clang-3.4 -g -c -emit-llvm lazy.c
brt-prep -trace=bblk lazy.bc
