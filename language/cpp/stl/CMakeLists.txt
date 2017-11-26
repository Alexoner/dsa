# all the examples are from www.geeksforgeeks.com
add_executable(pair pair.cpp)
add_executable(map map.cpp)
add_executable(debugCopy debugCopy.cpp)
target_link_libraries(debugCopy easylogging)

add_executable(closure closure.cpp)

add_executable(numeric numeric.cpp)
target_link_libraries(numeric easylogging)
