#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(pg-klee main.cpp jsoncpp.cpp)

if (${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
  message(FATAL_ERROR "pg-klee requires at least LLVM version 3.4")
endif()

set(KLEE_LIBS
  kleeCore
)

target_link_libraries(pg-klee ${KLEE_LIBS} ${Boost_LIBRARIES})

install(TARGETS pg-klee RUNTIME DESTINATION bin)

# The PG-KLEE binary depends on the runtimes
add_dependencies(pg-klee BuildKLEERuntimes)
