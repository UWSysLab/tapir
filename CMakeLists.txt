# Tapir
set(TAPIR_DIR ${CMAKE_CURRENT_SOURCE_DIR})
add_custom_target(tapir-posix
  COMMAND DMTR_CFLAGS=-I${CMAKE_SOURCE_DIR}/include DMTR_LDFLAGS='-L${PROJECT_BINARY_DIR}/libos/posix -ldmtr-libos-posix -Wl,-rpath,${PROJECT_BINARY_DIR}/libos/posix -L${CMAKE_SOURCE_DIR}/submodules/Hoard/src -lhoard -Wl,-rpath,${CMAKE_SOURCE_DIR}/submodules/Hoard/src' make
  WORKING_DIRECTORY ${TAPIR_DIR}
)
add_dependencies(tapir-posix dmtr-libos-posix)

#
# todo: is there a way to get this to run on `make clean`?
add_custom_target(tapir-posix-clean
    COMMAND make clean
    WORKING_DIRECTORY ${TAPIR_DIR}
)
