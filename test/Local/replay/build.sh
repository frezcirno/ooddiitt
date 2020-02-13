#!/usr/bin/env bash

rm -rf brt-out-tmp

clang-3.4 -emit-llvm -g -c replay.c
brt-prep -trace=bblk replay.bc
brt-igen -entry-point=foo00 brt-out-tmp/replay.bc
brt-igen -entry-point=main brt-out-tmp/replay.bc
