#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

add_executable(brt-icmp main.cpp StateComparison.cpp)

if (${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
  message(FATAL_ERROR "brt-rply requires at least LLVM version 3.4")
endif()

set(KLEE_LIBS
  kleeCore
  kleeJson
)

target_link_libraries(brt-icmp ${KLEE_LIBS} ${Boost_LIBRARIES})

install(TARGETS brt-icmp RUNTIME DESTINATION bin)

# The brt-icmp binary depends on the runtimes
add_dependencies(brt-icmp BuildKLEERuntimes)
