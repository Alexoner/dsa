# compiler
sudo apt install --no-install-recommends clang clang-format

# debugger

## gdb
Compile the binaries with debug symbols, and run it with gdb.

### Start a program

#### Interactive mode

    gdb binary

#### Execute commands at startup

    gdb binary --ex "run <--args>"

Or run a script:

    #!/bin/sh
    # file: debug
    ARGS=${@:2}
    gdb $1 -ex "${ARGS}"

### [find out while line number of code triggered segment fault](https://stackoverflow.com/questions/505465/line-number-of-segmentation-fault)
Run the program with gdb. 
When it caught SIGSEGV, enter "where" in gdb.
```shell
$ gdb blah
(gdb) run
(gdb) where
```

### [Dump all thread stack to a file](https://stackoverflow.com/questions/26805197/how-to-pipe-gdbs-full-stack-trace-to-a-file)
```shell
$ gdb <binary> core.dump
gdb> set logging on
gdb> set pagination off
gdb> thread apply all full bt
```
## gcore

## eu-stack

# Profiling tools
[gprof, valgrind, gperftools](http://gernotklingler.com/blog/gprof-valgrind-gperftools-evaluation-tools-application-level-cpu-profiling-linux/)

## [gperftools](https://github.com/gperftools/gperftools/wiki)
sudo apt install --no-install-recommends libgoogle-perftools-dev


## valgrind
sudo apt install --no-install-recommends valgrind
sudo apt install --no-install-recommends graphviz kcachegrind

This tools can debug memory errors(memory leak, bad access, segmentation fault...) and do other diagnostics.

Reference: 
https://www.ibm.com/developerworks/community/blogs/6e6f6d1b-95c3-46df-8a26-b7efd8ee4b57/entry/detect_memory_leaks_with_memcheck_tool_provided_by_valgrind_part_i8?lang=en

### common usage
```shell
valgrind ./executable # memory check
valgrind --leak-check=full # memory check
valgrind --track-origin=yes --leak-check=yes ./executable
valgrind --tool=callgrind ./executable # function and memory profiler
valgrind --tool=cachegrind --branch-sim=yes --cache-sim=yes bin/falseSharing # Cachegrind, a cache and branch-prediction profiler
valgrind --tool=drd --read-var-info=yes # drd(data race detection), a thread error detector
```

### FAQ
#### Valgrind on OSX reports false positive memory leak
ImageLoader is part of the OS X runtime and is responsible for loading binaries and dynamic libraries. It allocates some memory once, during initialization and forgets about it, but it's harmless because it's a small block of memory allocated only once. And it does a bunch of things that Valgrind doesn't like but that aren't incorrect.

# Monitor

## Grafana
https://github.com/grafana/grafana

## influxdb
time series database

# ops tools

- htop
- iftop
- iotop
- nvidia-smi
- tcpdump
