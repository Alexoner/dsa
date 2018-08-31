# all the examples are from www.geeksforgeeks.com
add_executable(pair pair.cpp)
add_executable(map map.cpp)
add_executable(set set.cpp)
add_executable(debugCopy debugCopy.cpp)
add_executable(queue queue.cpp)
target_link_libraries(debugCopy easylogging)

add_executable(closure closure.cpp)
add_executable(move move.cpp)

add_executable(numeric numeric.cpp)
add_executable(transform transform.cpp)
add_executable(vector vector.cpp)
add_executable(bind bind.cpp)
target_link_libraries(numeric easylogging)
