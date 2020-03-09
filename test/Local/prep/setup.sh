
rm -rf *.bc brt-out-tmp

IGEN_FLAGS="-progression=g:300"

clang-3.4 -g -c -emit-llvm pre-prep.c post-prep.c
brt-prep -trace=bblk pre-prep.bc post-prep.bc
