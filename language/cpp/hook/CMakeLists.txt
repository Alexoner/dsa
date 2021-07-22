# Add the -std=c++11 flag as an example

add_library(hook SHARED hook.c)
add_library(memcpy SHARED memcpy.cpp)
#set_target_properties(hook PROPERTIES COMPILE_FLAGS "" LINK_FLAGS "-ldl")
target_link_libraries(hook "dl") # link against "-ldl" for dlfcn
add_library(sched SHARED sched.cpp)
add_library(futex SHARED futex.cpp)

#add_executable(test_hook test_hook.cpp)
#set_target_properties(test_hook PROPERTIES COMPILE_FLAGS "" LINK_FLAGS "-ldl") # use LD_PRELOAD to inject

add_executable(test_hook test_hook.cpp memcpy.cpp)
set_target_properties(test_hook PROPERTIES COMPILE_FLAGS "-DBOOST_STACKTRACE_USE_ADDR2LINE" LINK_FLAGS "-Xlinker --wrap=memcpy -Wl,--no-as-needed -ldl") # using ld -wrap
#set_target_properties(test_hook PROPERTIES COMPILE_FLAGS "-DBOOST_STACKTRACE_USE_ADDR2LINE -DBOOST_STACKTRACE_LINK -DBOOST_STACKTRACE_USE_BACKTRACE -rdynamic" LINK_FLAGS "-Xlinker --wrap=memcpy -ldl -lboost_stacktrace_addr2line")
