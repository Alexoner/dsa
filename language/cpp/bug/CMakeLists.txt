add_executable(memory_leak memory_leak.cpp)
#set_target_properties(memory_leak PROPERTIES LINK_FLAGS "-ltcmalloc")
target_link_libraries(memory_leak "tcmalloc")
add_executable(dead_loop_and_memory_leak dead_loop_and_memory_leak.cpp)
set_target_properties(dead_loop_and_memory_leak PROPERTIES 
    COMPILE_FLAGS "-fsanitize=leak -O1" 
    LINK_FLAGS "-fsanitize=leak")
add_executable(use_after_free use_after_free.cpp)
set_target_properties(use_after_free PROPERTIES 
    COMPILE_FLAGS "-fsanitize=address" 
    LINK_FLAGS "-fsanitize=address")

add_executable(use_after_scope use_after_scope.cpp)
set_target_properties(use_after_scope PROPERTIES 
    COMPILE_FLAGS "-fsanitize=address -fsanitize-address-use-after-scope" 
    LINK_FLAGS "-fsanitize=address")
add_executable(use_after_scope_multithreads use_after_scope_multithreads.cpp)
set_target_properties(use_after_scope_multithreads PROPERTIES 
    COMPILE_FLAGS "-fsanitize=address -fsanitize-address-use-after-scope" 
    LINK_FLAGS "-fsanitize=address")

add_executable(data_race data_race.c)
set_target_properties(data_race PROPERTIES 
    COMPILE_FLAGS "-fsanitize=thread -O1" 
    LINK_FLAGS "-fsanitize=thread")

add_executable(deadlock deadlock.cpp)
set_target_properties(deadlock PROPERTIES 
    COMPILE_FLAGS "-fsanitize=thread -O1" 
    LINK_FLAGS "-fsanitize=thread")
