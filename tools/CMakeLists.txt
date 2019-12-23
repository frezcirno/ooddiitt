#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_subdirectory(brt-prep)
add_subdirectory(brt-icmp)
add_subdirectory(brt-igen)
add_subdirectory(brt-rply)
add_subdirectory(brt-rcrd)

install(PROGRAMS scripts/brt-dis DESTINATION bin)
