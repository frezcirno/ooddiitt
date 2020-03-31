
rm -rf *.bc brt-out-tmp

clang-3.4 -g -c -emit-llvm loop-boom.c
brt-prep -trace=bblk loop-boom.bc
