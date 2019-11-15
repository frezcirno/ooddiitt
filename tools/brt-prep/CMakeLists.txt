#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(brt-prep main.cpp jsoncpp.cpp)

if (${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
  message(FATAL_ERROR "brt-prep requires at least LLVM version 3.4")
endif()

set(KLEE_LIBS
  kleeCore
)

target_link_libraries(brt-prep ${KLEE_LIBS} ${Boost_LIBRARIES})

install(TARGETS brt-prep RUNTIME DESTINATION bin)

# The brt-prep binary depends on the runtimes
add_dependencies(brt-prep BuildKLEERuntimes)
