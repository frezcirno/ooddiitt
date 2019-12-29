#!/usr/bin/env bash

clang-3.4 -emit-llvm -g -c replay.c
brt-prep -trace-bblk replay.bc
brt-igen -entry-point=foo00 brt-out-tmp/replay.bc
