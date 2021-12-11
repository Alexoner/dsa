cmake_minimum_required(VERSION 2.6)

# The version number.
set (DSA_VERSION_MAJOR 1)
set (DSA_VERSION_MINOR 0)

#=============================================================================================
# project settings 
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

# use clang instead of gcc
#set(CMAKE_C_COMPILER "clang")
#set(CMAKE_CXX_COMPILER "clang++")
set(CMAKE_CXX_COMPILER "g++") # to enable sanitizer(-fsanitizer=thread,address), gcc>=6 is recommended


##################################### OS specific ############################################
if(WIN32)
    # for Windows operating system in general
endif()

# or
#if(MSVS OR MSYS OR MINGW)
    ## for detecting Windows compilers
#endif()

# Apple MacOS
if(APPLE)
    # for MacOS X
endif()

# Detect Unix and Linux 
if(UNIX AND NOT APPLE)
    # for Linux, BSD, Solaris, Minix
endif()

############################### build architecture ########
if (NOT BUILD_ARCH)
    set(BUILD_ARCH "-m64")
endif ()
message(STATUS "Build architecture: ${BUILD_ARCH}")

############################ BUILD TYPE and FLAGS ###################
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
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS} -std=c++11 -O0 -g -Wall -Wextra -fno-omit-frame-pointer") # address sanitizer, linking against libasan, slows down program
#set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS} -std=c++11 -O0 -g -Wall -Wextra -fsanitize=address") # address sanitizer, linking against libasan, slows down program
#set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS} -std=c++11 -O0 -g -Wall -Wextra -fsanitize=leak") # leak sanitizer, linking liblsan. `LD_PRELOAD=/usr/lib/x86_64-linux-gnu/liblsan.so.0 ./a.out`
#set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS} -std=c++11 -O0 -ggdb -Wall -Wextra -Wno-unused-result -Wreturn-type -Wmain -Werror=return-type -Werror=main -fsanitize=address")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS} -std=c++11 -O3")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -ggdb -Wall -std=c++11")

message(STATUS "[root] Build type: ${CMAKE_BUILD_TYPE}")

# thread library
set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
link_libraries(Threads::Threads)

if (CMAKE_BUILD_TYPE MATCHES "DEBUG")
    message(STATUS "[root] Build flags for debug: ${CMAKE_CXX_FLAGS_DEBUG}")

    set( CMAKE_EXPORT_COMPILE_COMMANDS ON ) # export compilation database

    option (WITH_PROFILE "build profiler" OFF) 
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

##################################### HEADERS ####

include_directories(language/cpp/include/)
include_directories(/home/hao.du/.linuxbrew/Cellar/boost/1.68.0_1/include/boost/)
link_directories(/home/hao.du/.linuxbrew/Cellar/boost/1.68.0_1/lib/)

############################ LOGGER #################
#if (NOT WITH_LOGGER)
  #SET(WITH_LOGGER "ON")
#endif()

# Options: control statement
option (WITH_LOGGER "build logger" ON) 

# link logging library
message(STATUS "WITH_LOGGER: " ${WITH_LOGGER})
if (WITH_LOGGER STREQUAL "ON") # or use MATCHES instead of STREQUAL
  message(STATUS "add library easylogging++")

  if (APPLE)
      add_library(easylogging STATIC language/cpp/logger/easylogging++.cc)
  else()
      add_library(easylogging SHARED language/cpp/logger/easylogging++.cc)
  endif()

  include_directories(language/cpp/logger)
  #link_libraries(easylogging)
endif()

########################## TEST #####################
if (NOT DEFINED WITH_TESTS)
  if (CMAKE_BUILD_TYPE MATCHES "DEBUG")
    SET(WITH_TESTS "ON")
  endif()
endif()
message(STATUS "WITH_TESTS: ${WITH_TESTS}")

########################## add sub-directories ##########
add_subdirectory (design/creational_pattern) 
add_subdirectory (design/behavioral_pattern) 
add_subdirectory (design/concurrency_pattern) 
add_subdirectory (oj/leetcode) 
#add_subdirectory (oj/questions) 
add_subdirectory (language/cpp)
add_subdirectory (questions/google)
add_subdirectory (questions/akunacapital)
add_subdirectory (parallel/cuda)
