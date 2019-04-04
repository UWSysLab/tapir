# Tapir
set(TAPIR_DIR ${CMAKE_CURRENT_SOURCE_DIR})

add_custom_target(tapir-rdma
  COMMAND DMTR_CFLAGS=-I${CMAKE_SOURCE_DIR}/include DMTR_LDFLAGS='-lrdmacm -libverbs -L${PROJECT_BINARY_DIR}/libos/rdma -ldmtr-libos-rdma -Wl,-rpath,${PROJECT_BINARY_DIR}/libos/rdma -L${CMAKE_SOURCE_DIR}/submodules/HoardRdma/src -lhoard -Wl,-rpath,${CMAKE_SOURCE_DIR}/submodules/HoardRdma/src' make
    WORKING_DIRECTORY ${TAPIR_DIR}
)
add_dependencies(tapir-rdma dmtr-libos-rdma)


#
# todo: is there a way to get this to run on `make clean`?
add_custom_target(tapir-rdma-clean
    COMMAND make clean
    WORKING_DIRECTORY ${TAPIR_DIR}
)
