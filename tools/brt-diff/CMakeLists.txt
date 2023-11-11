#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

add_executable(brt-diff main.cpp)

if (${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
  message(FATAL_ERROR "brt-diff requires at least LLVM version 3.4")
endif()

set(KLEE_LIBS
  kleeCore
  kleeJson
)

target_link_libraries(brt-diff ${KLEE_LIBS} ${Boost_LIBRARIES})

install(TARGETS brt-diff RUNTIME DESTINATION bin)

# The brt-diff binary depends on the runtimes
add_dependencies(brt-diff BuildKLEERuntimes)
