cmake_minimum_required(VERSION 2.6)

# The version number.
set (DSA_VERSION_MAJOR 1)
set (DSA_VERSION_MINOR 0)

#=============================================================================================
# project settings 
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

if (NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE "DEBUG")
endif (NOT CMAKE_BUILD_TYPE)


#Append Gperftools_DIR 
LIST(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake")

# compiler FLAGS
#set(CMAKE_CXX_FLAGS_DEBUG "put your flags")
#set(CMAKE_CXX_FLAGS_MINSIZEREL "put your flags")
#set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "put your flags")
#set(CMAKE_CXX_FLAGS_RELEASE "put your flags")
#set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS} -O0 -ggdb -Wall -Wextra -Werror -std=c++11")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS} -O0 -ggdb -Wall -Wextra -std=c++11")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS} -O3 -std=c++11")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -ggdb -Wall -std=c++11")

message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")

# thread library
set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
link_libraries(Threads::Threads)

if (CMAKE_BUILD_TYPE MATCHES "DEBUG")
    message(STATUS "Build flags for debug: ${CMAKE_CXX_FLAGS_DEBUG}")

    set( CMAKE_EXPORT_COMPILE_COMMANDS ON ) # export compilation database

    # google profiling tool: google perftools
    message(STATUS "WITH_PROFILE: " ${WITH_PROFILE})
    if (WITH_PROFILE MATCHES "ON")
      find_package(GooglePerftools)
      message(STATUS "Found google perftools: ${GOOGLEPERFTOOLS_FOUND}, ${GooglePerftools_LIBRARIES_DEBUG}")
      link_libraries(${GooglePerftools_LIBRARIES_DEBUG})
    endif()
else ()
    message(STATUS "Build flags for release: ${CMAKE_CXX_FLAGS_RELEASE}")
endif ()

if (NOT WITH_LOGGER)
  SET(WITH_LOGGER "ON")
endif()

# link logging library
message(STATUS "WITH_LOGGER: " ${WITH_LOGGER})
if (WITH_LOGGER STREQUAL "ON") # or use MATCHES instead of STREQUAL
  message(STATUS "add library easylogging++")
  add_library(easylogging SHARED language/cpp/logger/easylogging++.cc)
  include_directories(language/cpp/logger)
  link_libraries(easylogging)
endif()


if (NOT BUILD_ARCH)
    set(BUILD_ARCH "-m64")
endif ()
message(STATUS "Build architecture: ${BUILD_ARCH}")

add_subdirectory (design/creational_pattern) 
add_subdirectory (design/behavioral_pattern) 
add_subdirectory (design/concurrency_pattern) 
add_subdirectory (oj/leetcode) 
add_subdirectory (oj/questions) 
add_subdirectory (language/cpp)
