Linux debug, profile, performance tuning tools
==============================================

Table of Contents
=================

   * [Linux debug, profile, performance tuning tools](#linux-debug-profile-performance-tuning-tools)
   * [Table of Contents](#table-of-contents)
      * [Compiler](#compiler)
      * [Debugger(ptrace), profiler](#debuggerptrace-profiler)
         * [gdb](#gdb)
            * [Start gdb](#start-gdb)
            * [Execute commands at startup](#execute-commands-at-startup)
            * [Essential commands and common practices](#essential-commands-and-common-practices)
            * [GUI](#gui)
            * [<a href="https://stackoverflow.com/questions/26805197/how-to-pipe-gdbs-full-stack-trace-to-a-file" rel="nofollow">Dump all thread stack to a file</a>](#dump-all-thread-stack-to-a-file)
            * [Modifying program state](#modifying-program-state)
            * [<a href="https://unix.stackexchange.com/questions/166541/how-to-know-where-a-program-is-stuck-in-linux" rel="nofollow">Stack trace of running program</a>](#stack-trace-of-running-program)
         * [ptrace(strace &amp; ltrace)](#strace--ltrace)
         * [Core dump](#core-dump)
         * [ld.so &amp; ld](#ldso--ld)
            * [LD_PRELOAD](#ld_preload)
            * [ld --wrap=symbol](#ld---wrapsymbol)
      * [Linux administrative tools](#linux-administrative-tools)
         * [taskset - set or retrieve a process's CPU affinity](#taskset---set-or-retrieve-a-processs-cpu-affinity)
            * [Read the CPU Affinity of a Running Process](#read-the-cpu-affinity-of-a-running-process)
            * [Pin a Running Process to Particular CPU Core(s)](#pin-a-running-process-to-particular-cpu-cores)
            * [Launch a Program on Specific CPU Cores](#launch-a-program-on-specific-cpu-cores)
         * [iptables - administrative tool for IPv4/IPv6 packet filtering and NAT](#iptables---administrative-tool-for-ipv4ipv6-packet-filtering-and-nat)
         * [tc - traffic control](#tc---traffic-control)
         * [pmap - report memory map of a process](#pmap---report-memory-map-of-a-process)
         * [ps &amp; top &amp; htop](#ps--top--htop)
            * [memory](#memory)
         * [dmesg](#dmesg)
      * [Text processing command line tools](#text-processing-command-line-tools)
         * [Search tools](#search-tools)
            * [ag](#ag)
            * [egrep](#egrep)
         * [Edit tools](#edit-tools)
            * [find](#find)
            * [sed](#sed)
            * [awk](#awk)
         * [sort](#sort)
         * [uniq - report or omit repeated lines](#uniq---report-or-omit-repeated-lines)
         * [eu-stack](#eu-stack)
      * [Parallel processing](#parallel-processing)
         * [background task with &amp;](#background-task-with-)
         * [parallel](#parallel)
         * [xargs](#xargs)
      * [File system](#file-system)
         * [/proc/$PID/](#procpid)
         * [/var/log/auth.log - system authentication log](#varlogauthlog---system-authentication-log)
      * [Static analysis tool](#static-analysis-tool)
         * [cppcheck](#cppcheck)
         * [clang-tools](#clang-tools)
      * [Quality assurance tools](#quality-assurance-tools)
         * [<a href="https://github.com/google/sanitizers">Sanitizers</a>](#sanitizers)
            * [How to check memory of a running process - Use gdb to call check function?](#how-to-check-memory-of-a-running-process---use-gdb-to-call-check-function)
            * [Control flow sanitizer](#control-flow-sanitizer)
            * [Stack buffer overflow](#stack-buffer-overflow)
         * [Testing](#testing)
            * [Unittest](#unittest)
            * [Fuzz testing(fuzzing/fuzzer)](#fuzz-testingfuzzingfuzzer)
      * [Profiling tools](#profiling-tools)
         * [<a href="https://github.com/gperftools/gperftools/wiki">gperftools</a>](#gperftools)
            * [Install](#install)
            * [TC malloc](#tc-malloc)
            * [Heap checker](#heap-checker)
            * [Heap profiler](#heap-profiler)
               * [Call api](#call-api)
            * [Cpu Profiler](#cpu-profiler)
            * [Analyze dumped file with pprof](#analyze-dumped-file-with-pprof)
            * [Best practice](#best-practice)
         * [valgrind](#valgrind)
            * [common usage](#common-usage)
            * [FAQ](#faq)
               * [Valgrind on OSX reports false positive memory leak](#valgrind-on-osx-reports-false-positive-memory-leak)
      * [Other ops tools](#other-ops-tools)
         * [netstat](#netstat)
         * [lsof](#lsof)
      * [production tools](#production-tools)
         * [Monitor tools](#monitor-tools)
            * [Grafana - analytics and monitoring](#grafana---analytics-and-monitoring)
            * [influxdb - time series database](#influxdb---time-series-database)

Created by [gh-md-toc](https://github.com/ekalinin/github-markdown-toc)

Compiler
--------

    sudo apt install --no-install-recommends clang gcc-7

Debugger(ptrace), profiler
--------------------------

Linux administrative tools
--------------------------

### `taskset` - set or retrieve a process's CPU affinity

### `iptables` - administrative tool for IPv4/IPv6 packet filtering and NAT
### tc - traffic control

### pmap - report memory map of a process

    pmap -x pid

### ps & top & htop

### Misc

    # set run timeout for a process with timeout
	timeout 1s ./a.out
	timeout --signal=HUP 1s ./a.out # set run timeout for a process
	# set CPU time limit with ulimit -t


Text processing command line tools
---------------------------------

### PIPE


### while 

    # heredoc piped into while read
    # heredoc with indentation of tab, piped into while, split string with IFS
    IFS=" " cat <<-EOF | while read a b c d
    1 2 3 4 
    5 6 7 8
    EOF
    do echo $a,$b,$c,$d
    done | parallel echo "processing {}"

### Search tools

#### ag

    # search for class definition
    ag '(struct|class|enum|(typedef.*)) RetrieveOption'

#### egrep

    grep 'pattern' ${input} # text pattern
    egrep 'pattern' ${input} # regular expression pattern
- -o: only show matching portion
- --color: colorful display
- -a: number of lines after
- -C: context number

### Edit tools

#### cat & tac
cat: catenate files and print
tac: catenate and print in reverse

#### find

#### awk
A versatile programming language.

### sort

### uniq - report or omit repeated lines

### eu-stack
TODO

Parallel processing
-------------------
- Use GNU/parallel or xargs command.
- Use wait built-in command with &.
- Use xargs command.

### background task with `&`

    prog1 &

###  `parallel`
### `xargs`
Sequentially execute batch tasks.

### `find`


File system
------------

### `/proc/$PID/`

### `/var/log/auth.log` - system authentication log

For example, if someone used `sudo kill` to kill your process behind you, you can check it out there.

### `/sys/devices/`

### `/sys/devices/system/cpu/cpu0/cache/`

Static analysis tool
--------------------

### cppcheck

### clang-tools

### gcc

    g++ -fdump-class-hierachy a.cpp # show class hiearchy
    g++ -g -std=c++11 -Weffc++ a.cpp # -g for debug, -Weffc++ 

Quality assurance tools
-----------------------

### [Sanitizers](https://github.com/google/sanitizers)

- ASan: Address Sanitizer detects use-after-free, buffer-overflow, and leaks.
- TSAN: Thread Sanitizer detects data races, deadlocks.
- MSAN: Memory Sanitizer detects uses of uninitialized memory.
- UBSan: Undefined Behavior Sanitizer detects… that


Profiling tools
---------------

There are two kinds of profilers:
- Sampling based
- Event based (tracing, instrument)


Gprof, Gcov, gperftools, perf_events

Reference:
[gprof, valgrind, gperftools](http://gernotklingler.com/blog/gprof-valgrind-gperftools-evaluation-tools-application-level-cpu-profiling-linux/), [perf_events](http://www.brendangregg.com/perf.html)

### [gperftools](https://github.com/gperftools/gperftools/wiki)
### valgrind

Linux Tracing tools
-------------------

### ptrace, strace

### ftrace

#### trace-cmd

#### perf-tools(https://github.com/brendangregg/perf-tools)

#### kernelshark

#### uprobe

TODO

Development tools
-----------------

### git

#### log 

#### FAQ
##### Valgrind on OSX reports false positive memory leak
ImageLoader is part of the OS X runtime and is responsible for loading binaries and dynamic libraries. It allocates some memory once, during initialization and forgets about it, but it's harmless because it's a small block of memory allocated only once. And it does a bunch of things that Valgrind doesn't like but that aren't incorrect.

Other ops tools
----------------

https://www.thegeekstuff.com/2011/12/linux-performance-monitoring-tools
https://www.tecmint.com/command-line-tools-to-monitor-linux-performance/

CPU     	 htop, top
GPU     	 gpu
process 	 ps, pstree
debug   	 gdb, ptrace(strace), perf, dtrace
memory  	 htop, free, pmap, vmstat
disk    	 df, du, iotop, iostat
network 	 nc, ping, iperf, iftop, nload, netstat, sar, tcpdump
misc    	 dstat, lsof, cat /proc

- htop
- [iftop](https://www.systutorials.com/docs/linux/man/8-iftop/)
- iotop
- nvidia-smi
- tcpdump


### netstat - Print network connections, routing tables, interface statistics, masquerade connections, and multicast memberships

    netstat -nlpte # list all listenig ports

- -n: numeric
- -l: listening
- -t: tcp
- -e: extend, display additional info

### lsof - list open files

	man lsof # man page
	lsof # list all open files
	lsof -u $USERNAME # list files opened by specific user, inclusively or exclusively
	lsof -i 4 # list IPv4 socket files. -i specifier form: [46][protocol][@hostname|hostaddr][:service|port]
	lsof -i 6 # list IPv6 socket files
	lsof -i :1-1024 # list open files based on port range 1-1024
    lsof -p $PID # list open files specific to a process with $PID, inclusively or exclusively
	lsof $FILENAME # list all processes that opened $FILENAME, inclusively or exclusively

Reference:
https://www.howtoforge.com/linux-lsof-command/

# mount & umount
Used to mount files systems, both system or user space file system(fuse).



production tools
-----------------
- mongodb
    - robo 3T

### Monitor tools

#### Grafana - analytics and monitoring
https://github.com/grafana/grafana

#### influxdb - time series database
time series database
