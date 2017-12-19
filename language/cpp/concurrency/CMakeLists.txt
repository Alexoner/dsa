add_executable(helloConcurrency helloConcurrency.cpp)
add_executable(threads threads.cpp)
add_executable(atomicOperation atomicOperation.cpp)

#set_target_properties(atomicOperation PROPERTIES COMPILE_FLAGS "${BUILD_ARCH} -std=c++11 -O0" LINK_FLAGS ${BUILD_ARCH})
