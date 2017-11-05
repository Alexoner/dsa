# Profiling tools
[gprof, valgrind, gperftools](http://gernotklingler.com/blog/gprof-valgrind-gperftools-evaluation-tools-application-level-cpu-profiling-linux/)

## [gperftools](https://github.com/gperftools/gperftools/wiki)


## valgrind

This tools can debug memory errors(memory leak, bad access, segmentation fault...) and do other diagnostics.

Reference: 
https://www.ibm.com/developerworks/community/blogs/6e6f6d1b-95c3-46df-8a26-b7efd8ee4b57/entry/detect_memory_leaks_with_memcheck_tool_provided_by_valgrind_part_i8?lang=en

### 
valgrind ./executable
valgrind --tool=callgrind ./executable
valgrind --leak-check=yes ./executable

