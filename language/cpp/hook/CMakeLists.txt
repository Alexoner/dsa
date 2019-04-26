# Add the -std=c++11 flag as an example

#add_library(hook SHARED hook.c)
add_library(hook SHARED memcpy.cpp)
target_link_libraries(hook "dl") # link against "-ldl" for dlfcn

# stl
#add_subdirectory(bug)

