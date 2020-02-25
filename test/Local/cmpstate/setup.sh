
rm -rf *.bc brt-out-tmp

clang-3.4 -g -c -emit-llvm pre-state.c post-state.c
brt-prep -trace=bblk pre-state.bc post-state.bc

for ver in "pre" "post"; do
#  brt-igen -entry-point=foo01 brt-out-tmp/${ver}-state.bc
#  brt-igen -entry-point=foo02 brt-out-tmp/${ver}-state.bc
  brt-igen -entry-point=foo03 brt-out-tmp/${ver}-state.bc
#  brt-igen -entry-point=main brt-out-tmp/${ver}-state.bc
done
