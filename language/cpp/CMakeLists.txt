if (NOT BUILD_ARCH)
	set(BUILD_ARCH "-m64")
endif ()

add_executable(nestedException nestedException.cpp)
add_executable(vptr vptr.cpp)
# Add the -std=c++11 flag as an example
#set_source_files_properties( vptr.cpp PROPERTIES COMPILE_FLAGS "-m32 -std=c++11" )
#set_target_properties(vptr PROPERTIES COMPILE_FLAGS "-std=c++11")

set_target_properties(vptr PROPERTIES COMPILE_FLAGS "${BUILD_ARCH} -std=c++11" LINK_FLAGS ${BUILD_ARCH})
add_executable(callCFunction callCFunctionCPP.cpp callCFunctionC.c)
add_executable(virtualFunction virtualFunction.cpp)
add_executable(typePromotion typePromotion.cpp)
add_executable(destructionOrder destructionOrder.cpp)
add_executable(isDerivedFrom isDerivedFrom.cpp)

# stl
add_subdirectory(stl)
