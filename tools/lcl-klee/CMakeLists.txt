#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(lcl-klee
  main.cpp jsoncpp.cpp
        ../../include/klee/Internal/System/Marker.h)

if (${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
  message(FATAL_ERROR "opt-klee requires at least LLVM version 3.4")
endif()

set(KLEE_LIBS
  kleeCore
)

target_link_libraries(lcl-klee ${KLEE_LIBS} ${Boost_LIBRARIES})

install(TARGETS lcl-klee RUNTIME DESTINATION bin)

# The KLEE binary depends on the runtimes
add_dependencies(lcl-klee BuildKLEERuntimes)
