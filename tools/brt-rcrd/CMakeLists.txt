#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(brt-rcrd main.cpp jsoncpp.cpp)

if (${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
  message(FATAL_ERROR "brt-rcrd requires at least LLVM version 3.4")
endif()

set(KLEE_LIBS
  kleeCore
)

target_link_libraries(brt-rcrd ${KLEE_LIBS} ${Boost_LIBRARIES})

install(TARGETS brt-rcrd RUNTIME DESTINATION bin)

# The brt-rcrd binary depends on the runtimes
add_dependencies(brt-rcrd BuildKLEERuntimes)
