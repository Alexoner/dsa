add_executable(helloConcurrency helloConcurrency.cpp)
add_executable(threads threads.cpp)
add_executable(atomicOperation atomicOperation.cpp)
add_executable(falseSharing falseSharing.cpp)
add_executable(promise promise.cpp)
add_executable(call_once call_once.cpp)
add_executable(gettime gettime.cpp)

#set_target_properties(atomicOperation PROPERTIES COMPILE_FLAGS "${BUILD_ARCH} -std=c++11 -O0" LINK_FLAGS ${BUILD_ARCH})
