set(CMAKE_C_COMPILER "mpicc")

include_directories(/usr/lib/x86_64-linux-gnu/openmpi/include/)

add_executable(mpi_hello_world mpi_hello_world.c)
