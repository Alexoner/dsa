# compiler

	sudo apt install --no-install-recommends clang gcc-7

# debugger

## gdb
Compile the binaries with debug symbols, and run it with gdb.

### Attach a program

#### Interactive mode

    gdb [prog|prog procID|prog core]
    gdb program
    gdb program core
    gdb program pid
    gdb -p $PID

#### Execute commands at startup

    gdb program --ex "run <--args>"

Or run a script:

```shell
#!/bin/sh
# file: debug

ARGS=${@:2}
gdb $1 -ex "${ARGS}"
```

### Essential commands

```shell
$ gdb program (pid)
gdb> run
gdb> where # print backtrace of all stack frames
gdb> layout src # enter TUI mode
gdb> s # step into function
gdb> return # make current function return, popping out of stack frame
gdb> n # next statement, step over
gdb> set variable $address = &i # get address of i in process
gdb> set variable {int}$address = 999 # To store values into arbitrary places in memory, use the ‘{…}’ construct to generate a value of specified type at a specified address (see Expressions). For example, {int}0x83040 refers to memory location 0x83040 as an integer (which implies a certain size and representation in memory), and
gdb> print i
0
gdb> print pa # print shared_ptr<type> pa
$4 = std::shared_ptr<A> (use count 1, weak count 0) = {get() = 0x603000000010}
gdb> print pa->name
A
gdb> print *pa
$5 = {name = "A"}
gdb> c # continue
gdb> #b ... # break at somewhere
gdb> whatis i
type = int
gdb> print i
0
gdb> set variable i = -1
gdb> print i
-1
gdb> call i = 1 + 1 # execute/call statement
gdb> print i
2
gdb> set variable $i = (int)i # $i assign a process's variable to gdb shell variable
gdb> print $i
2
gdb> call printf("xxxxxx") # execute/call function

```

Refrence
--------
- https://sourceware.org/gdb/onlinedocs/gdb/Assignment.html
- https://sourceware.org/gdb/onlinedocs/gdb/Compiling-and-Injecting-Code.html
- https://www.codeproject.com/Articles/33340/Code-Injection-into-Running-Linux-Application
- https://blogs.oracle.com/linux/8-gdb-tricks-you-should-know-v2

### [Dump all thread stack to a file](https://stackoverflow.com/questions/26805197/how-to-pipe-gdbs-full-stack-trace-to-a-file)
```shell
$ gdb <binary> core.dump
gdb> set logging on
gdb> set pagination off
gdb> thread apply all full bt
```

### Modifying program state


## `/proc/$PID/`

Experiment:
Run `deadloop` and experiment with those tools.

1. `/proc/$PID/cmdline`: command line that started this process
2. `/proc/$PID/status`: VmSize for memory usage?
3. `/proc/$PID/exe`: `realpath /proc/$PID/exec` the program being run.
4. `/proc/$PID/stat`: 14 system time, 15 user time, blah blah.. `pidstat` is an easier tool.
5. `/proc/$PID/environ`: `cat /proc/37517/environ|tr '\0' '\n'` to display environment variables of a running process.

## Frequent situations 

### [Stack trace of running program](https://unix.stackexchange.com/questions/166541/how-to-know-where-a-program-is-stuck-in-linux)
#### `gdb`
1. Direct use of gdb

Run the program with gdb. 
When it caught `SIGSEGV`, enter `where` in gdb.

[stack frame](https://stackoverflow.com/questions/505465/line-number-of-segmentation-fault)

```shell
linux:~ # sleep 3600 &
 [2] 2621
 tweedleburg:~ # sudo gdb
 (gdb) attach 2621
 (gdb) bt
 #0  0x00007feda374e6b0 in __nanosleep_nocancel () from /lib64/libc.so.6
 #1  0x0000000000403ee7 in ?? ()
 #2  0x0000000000403d70 in ?? ()
 #3  0x000000000040185d in ?? ()
 #4  0x00007feda36b8b05 in __libc_start_main () from /lib64/libc.so.6
 #5  0x0000000000401969 in ?? ()
 (gdb)
```

Use gdb to change environment variables of a running process.
```shell
(gdb) attach process_id

(gdb) call putenv ("env_var_name=env_var_value")

(gdb) detach
```

2. `pstack.sh`
This is a script using gdb to attach to a running process then get the process's
call stack.

#### strace & ltrace
`strace` can be used to trace system call and signals.

    strace -f -p -Ttt $PID -o app.strace

- -f: trace child processes, all threads
- -T: show time spent in system calls
- -t: prefix line with time of day
- -tt: macroseconds
- -o: output

#### Core dump
When a process runs into `segmentation fault`, the operating system can dump the process state.

Make sure `ulimit`  for core size is not 0.

	ulimit -c unlimited

Consider modify core dump file

	$ cat /proc/sys/kernel/core_pattern                                              │
	|/usr/share/apport/apport %p %s %c %d %P 

Generate a core file of a running program.

	sudo gcore [-o filename] pid

After a core dump file is generated, view it with `gdb`

	gdb <binary file> core

## [address sanitizer]()

This feature is supported by gcc/clang with higher version(gcc>=6).
Update compiler if necessary.

```cpp
/*
 * a.cpp
 */
#include <stdlib.h>

void *p;

int main() {
  p = malloc(7);
  p = 0; // The memory is leaked here.
  return 0;
}
```

Compile the source code with compiler's [sanitizer flags](https://github.com/google/sanitizers/wiki/AddressSanitizerFlags):

    g++ -std=c++11 -g -fsanitize=address a.cpp

Run the binary with appropriate `ASAN_OPTION`: 

    export ASAN_OPTIONS=detect_leaks=1:abort_on_error=1:disable_coredump=0:unmap_shadow_on_exit=1
    ./a.out

#### Use gdb to attach to a running process

To use address sanitizer or leak sanitizer under `ptrace`(gdb, strace), we need to set:

    export LSAN_OPTIONS=detect_leaks=0

Then use gdb:

    gdb -p pid
    (gdb) break __sanitizer::Die
    (gdb) c
    (gdb) call __lsan_do_leak_check () # tips: tab can complete


The problem is, where did the output go?


## pmap - report memory map of a process

    pmap -x pid

# Finding process/threads

### memory 

Sort processes by memory consumption

    ps aux |sort -k 4,4 -h -r |head

### top & htop

    top -H -p pid # only show process with pid and kernel process(cloned process, thread)
    htop -p pid


## dmesg
If a process is killed by the process, likely because of OOM(out of memory). 

Then messages like this is expected in `dmesg |tail -n 20`
```text
[2901452.813490] Out of memory: Kill process 28345 (deadloop) score 765 or sacrifice child
[2901452.813515] Killed process 28345 (deadloop) total-vm:21474908536kB, anon-rss:30564396kB, file-rss:4kB, shmem-rss:0kB
[2901454.892452] oom_reaper: reaped process 28345 (deadloop), now anon-rss:0kB, file-rss:0kB, shmem-rss:0kB 
```

# ld.so

    man 8 ld.so

`LD_PRELOAD` environment variable can be used to override functions in other libraries.

For example, setting to enable `leak sanitizer` we can do this:
    
    LD_PRELOAD=/usr/lib/x86_64-linux-gnu/liblsan.so.0 ./a.out

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

This seems to slow down the program significantly...

### FAQ
#### Valgrind on OSX reports false positive memory leak
ImageLoader is part of the OS X runtime and is responsible for loading binaries and dynamic libraries. It allocates some memory once, during initialization and forgets about it, but it's harmless because it's a small block of memory allocated only once. And it does a bunch of things that Valgrind doesn't like but that aren't incorrect.

# ops tools

https://www.thegeekstuff.com/2011/12/linux-performance-monitoring-tools
https://www.tecmint.com/command-line-tools-to-monitor-linux-performance/

CPU	htop, top
GPU	gpu
process	ps, pstree
debug	gdb, strace, perf, dtrace
memory	htop, free, pmap, vmstat
disk	df, du, iotop, iostat
network	nc, ping, iperf, iftop, nload, netstat, sar, tcpdump
misc	dstat, lsof, cat /proc

- htop
- iftop
- iotop
- nvidia-smi
- tcpdump

## production tools
- mongodb
    - robo 3T

## Monitor

### Grafana - analytics and monitoring
https://github.com/grafana/grafana

### influxdb - time series database
time series database


