#===-- runtime/Makefile ------------------------------------*- Makefile -*--===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

#
# Relative path to the top of the source tree.
#
LEVEL=..

#
# List all of the subdirectories that we will compile.
#
PARALLEL_DIRS=Intrinsic Intrinsic-32 Intrinsic-64 klee-libc Runtest

include $(LEVEL)/Makefile.config

ifeq ($(ENABLE_POSIX_RUNTIME),1)
PARALLEL_DIRS += POSIX POSIX-32 POSIX-64
endif

ifeq ($(ENABLE_UCLIBC),1)
PARALLEL_DIRS += klee-uclibc
endif

include $(LEVEL)/Makefile.common
