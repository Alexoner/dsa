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

### gdb
Compile the binaries with debug symbols, and run it with gdb.

#### Start gdb

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

#### Essential commands and common practices

```shell
$ gdb program (pid)
gdb> run
gdb> where # print backtrace of all stack frames
gdb> bt # backtrace, same as where
gdb> f n # select frame with number n.
gdb> up n # move n frames up the stack
gdb> down n # move n frames down the stack
gdb> layout src # enter TUI mode
gdb> s # step into function
gdb> return # make current function return, popping out of stack frame
gdb> n # next statement, step over
gdb> c # continue
gdb> set variable $address = &i # get address of i in process
gdb> set variable {int}$address = 999 # To store values into arbitrary places in memory
gdb> print i
0
gdb> print pa # print shared_ptr<type> pa
$4 = std::shared_ptr<A> (use count 1, weak count 0) = {get() = 0x603000000010}
gdb> print pa->name
A
gdb> print *pa
$5 = {name = "A"}
gdb> #b ... # break points at somewhere
gdb> break operator new # break at operator new
gdb> break mmap # break at mmap
# set break point on new_do_write if second register parameter string is "ERROR\n". $_streq is convenience function
gdb> b new_do_write if $_streq((char*)$rsi, "ERROR\n")
gdb> b __GI___libc_write if $x0 == 2 # set break point when writing to stderr(2), ARM register
# https://stackoverflow.com/questions/23757996/gdb-how-to-break-on-something-is-written-to-cout
gdb> b fwrite if $rcx==&_IO_2_1_stdout_
gdb> b fwrite if $rcx==&_IO_2_1_stderr_ # Intel register
gdb> info break # list breakpoints
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
gdb> print/s data # print as string format
$5 = 0x614c20 "hello world\n"
gdb> set variable $i = (int)i # $i assign a process's variable to gdb shell variable
gdb> print $i
2
gdb> call printf("xxxxxx") # execute/call function
gdb> compile  # compile C code
gdb> disassemble main # show assemble language representation of function main
gdb> info frame
gdb> info registers # show register values
gdb> info vtbl *pa # show virtual method table of C++ object *pa
gdb> x /4xw $rip # examin memory pointed by $rip (instruction register), 4 words hex
gdb> print /s $
gdb> x /s $rsi # examine memory address stored in register as string
0x614c20:       "begin().base0\n"
gdb> x/5i $rip # examine 5 instructions in register %rip

```

Connect to gdb server: 

```shell
sudo gdbserver --attach 0.0.0.0:8000 pid
gdb
gdb> target remote host:port
gdb> #...
```

Strategies to use gdb
- Use `strace` to monitor system calls, then set conditional break points in gdb
- Use `objdump` and `readelf` for static examination then gdb for runtime debugging

```shell
  > gcc -g -c test.c
  > objdump -d -M intel -S test.o
```


#### GUI

https://sourceware.org/gdb/wiki/GDB%20Front%20Ends

[gdbgui](https://github.com/cs01/gdbgui/) is awesome.

Refrence
- https://sourceware.org/gdb/onlinedocs/gdb/Assignment.html
- https://sourceware.org/gdb/onlinedocs/gdb/Compiling-and-Injecting-Code.html
- https://www.codeproject.com/Articles/33340/Code-Injection-into-Running-Linux-Application
- https://blogs.oracle.com/linux/8-gdb-tricks-you-should-know-v2

#### [Dump all thread stack to a file](https://stackoverflow.com/questions/26805197/how-to-pipe-gdbs-full-stack-trace-to-a-file)
```shell
$ gdb <binary> core.dump
gdb> set logging on
gdb> set pagination off
gdb> thread apply all full bt
gdb> thread n # select thread n
gdb> f m # select frame depth with number m
```

#### Modifying program state

```shell
gdb> call i = 0; # change variable i to 0
```
Abnormal program state and possible reasons
- Dirty data that doesn't make sense
    - Data race
    - Illegal memory access: object has been destroyed, so memory is used for other purpose.

#### [Stack trace of running program](https://unix.stackexchange.com/questions/166541/how-to-know-where-a-program-is-stuck-in-linux)

Underlying kernel api `ptrace` is needed to get the current stack trace/frame of a process.

1. Direct use of gdb

Run the program with gdb. 
When it caught `SIGSEGV`, enter `where` in gdb.


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

    (gdb) attach process_id
    (gdb) call putenv ("env_var_name=env_var_value")
    (gdb) detach

2. `pstack.sh`
This is a wrapper script using gdb to attach to a running process then get the process's
call stack.

### ptrace(strace & ltrace)
`strace` can be used to trace system call and signals.

    strace -Ttt -f -p $PID -o app.strace # print out syscall
    strace -w -c # show syscall latency

- -f: trace child processes, all threads
- -T: show time spent in system calls
- -t: prefix line with time of day
- -tt: macroseconds
- -o: output

### Core dump
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

### ld.so & ld

    man 8 ld.so
    man ld

#### LD_PRELOAD

`LD_PRELOAD` environment variable can be used to override functions in other libraries,
including `libc` system calls.

For example, setting to enable `leak sanitizer` we can do this:

    LD_PRELOAD=/usr/lib/x86_64-linux-gnu/liblsan.so.0 ./a.out

A sandbox environment can be created by overriding system calls with environment variable `LD_PRELOAD`.

#### ld --wrap=symbol

Use a wrapper function for symbol.
Any undefined reference to symbol will be resolved to "__wrap_symbol".  Any undefined reference to "__real_symbol" will be resolved to symbol.

This can be used to provide a wrapper for a system function.  The wrapper function should be called "__wrap_symbol".  If it wishes to call the system function, it should call
"__real_symbol".

Here is a trivial example:

    void *
    __wrap_malloc (size_t c)
    {
      printf ("malloc called with %zu\n", c);
      return __real_malloc (c);
    }

If you link other code with this file using --wrap malloc, then all calls to "malloc" will call the function "__wrap_malloc" instead.  The call to "__real_malloc" in "__wrap_malloc" will
call the real "malloc" function.

You may wish to provide a "__real_malloc" function as well, so that links without the --wrap option will succeed.  If you do this, you should not put the definition of "__real_malloc" in
the same file as "__wrap_malloc"; if you do, the assembler may resolve the call before the linker has a chance to wrap it to "malloc".


#### `mprotect`

    man mprotect

#### `electric-fence`

    man libefence


Linux administrative tools
--------------------------

### `taskset` - set or retrieve a process's CPU affinity

#### Read the CPU Affinity of a Running Process
To retrieve the CPU affinity of a process, you can use the following command.

    taskset -p [PID]

For example, to check the CPU affinity of a process with PID 1141.

    $ taskset -p 1141
    pid 1141's current affinity mask: ffffffff

The return value `ffffffff` is essentially a hexadecimal bitmask, corresponding to 1111 1111 1111 1111 1111 1111 1111 1111. Each bit in the bitmask corresponds to a CPU core. The bit value 1 means that the process can be executed on the corresponding CPU core. Therefore, in above example, pid 1141 can be executed on CPU core 0-31.

You may think that bitmask is a little hard to understand. Don’t worry. taskset can also show CPU affinity as a list of processors instead of a bitmask using “-c” option. An example is given as follows.

    $ taskset -cp 1141
    pid 1141's current affinity list: 0-31

#### Pin a Running Process to Particular CPU Core(s)
You can also use taskset to pin a running process to particular CPU core(s). The command formats are given as follows.

    taskset -p [CORE-LIST] [PID]
    taskset -cp [CORE-LIST] [PID]

For example, to assign process 1141 to CPU core 0 and 4:

    $ taskset -p 0x11 1141
    $ taskset -c -p 0-55 221441
    pid 221441's current affinity list: 0-63
    pid 221441's new affinity list: 0-55

Set CPU affinity of a process and all of its children threads:

    #!/bin/sh
    # file: limitcpu

    PID=$1
    NCORES=${2:-55}

    echo "taskset for pid: $PID, to number of cores: $NCORES"

    for pid in `ps -T ax |grep $PID |awk '{print $2}' |sort`
    do
        taskset -p -c 0-$((NCORES - 1)) $pid
    done


#### Launch a Program on Specific CPU Cores
`taskset` also allows us to launch a program running on specific CPU cores. The command is given as follows.

    taskset [COREMASK] [EXECUTABLE]

For example, to launch a ping program (destination 8.8.8.8) on a CPU core 0, use the following command.

    $ taskset 0x1 ping 8.8.8.8

Reference: https://baiweiblog.wordpress.com/2017/11/02/how-to-set-processor-affinity-in-linux-using-taskset/

### `iptables` - administrative tool for IPv4/IPv6 packet filtering and NAT
TODO

Drop packet from a server port:

    iptables -A INPUT --src $IP --port $PORT -j DROP
    iptables -A INPUT --src $IP --port $PORT --mode random --probability 0.9 -j DROP

### tc - traffic control

Rate limit for a specific host:

    #!/bin/sh
    # file: limittraffic


    DEVICE=bond0
    CLIENT_IP=${1:-10.40.46.23}

    echo "device: $DEVICE, IP: $CLIENT_IP"

    tc qdisc del dev $DEVICE root # delete root rule
    tc qdisc add dev $DEVICE root handle 1: htb default 10

    tc class add dev $DEVICE parent 1: classid 1:1 htb rate 1gbps ceil 1500mbps

    tc class add dev $DEVICE parent 1:1 classid 1:10 htb rate 1gbps ceil 1500mbps # default goes here

    tc class add dev $DEVICE parent 1:1 classid 1:11 htb rate 1gbps ceil 1gbps # matches limited IP goes here

    tc filter add dev $DEVICE protocol ip parent 1:0 prio 1 u32 match ip src ${CLIENT_IP} flowid 1:11
    tc filter add dev $DEVICE protocol ip parent 1:0 prio 1 u32 match ip dst ${CLIENT_IP} flowid 1:11

### pmap - report memory map of a process

    pmap -x pid

### ps & top & htop

`ps`:
- -T: show threads
- -e: select all process
- -f: full format
- -F: extra full format
- -p: select by pid list

```shell
    ps -TFe # list all threads, with extra full format of all processes
    ps -TF -p $PID # list all threads, with extra full format, of process $PID
    # a zombie process is already dead, but not waited by parent process. Kill its parent will let 'init' process take over
    kill $(ps -A -ostat,ppid | awk '/[zZ]/ && !a[$2]++ {print $2}') # [zZ] for pattern, a[$2]++ to filter duplicate ppid.
```

#### memory

Sort processes by memory consumption

    ps aux |sort -k 4,4 -h -r |head
    ps aux -T --sort=-%mem |less
    top -H -p pid # only show process with pid and kernel process(cloned process, thread)
    htop -p pid


### dmesg
If a process is killed by the process, likely because of OOM(out of memory). 

Then messages like this is expected in `dmesg |tail -n 20`

    [2901452.813490] Out of memory: Kill process 28345 (deadloop) score 765 or sacrifice child
    [2901452.813515] Killed process 28345 (deadloop) total-vm:21474908536kB, anon-rss:30564396kB, file-rss:4kB, shmem-rss:0kB
    [2901454.892452] oom_reaper: reaped process 28345 (deadloop), now anon-rss:0kB, file-rss:0kB, shmem-rss:0kB 


Text processing command line tools
---------------------------------

### PIPE
Pipe operator `|` in linux shell is very powerful.
Another useful tool is NAMED PIPE(`man mkfifo`), which create a virtual file
as a pipe in memory.

    # keep testing until fail
    while true; do ./program || break; done

### while 

    # heredoc piped into while read
    while true; do ./program || break; done # keep running a program until fail
    # heredoc with indentation of tab, piped into while, split string with IFS
    IFS=" " cat <<-EOF | while read a b c d
    1 2 3 4 
    5 6 7 8
    EOF
    do echo $a,$b,$c,$d
    done | parallel echo "processing {}"

### Search tools

#### ag

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

    find . -regextype posix-extended -regex '.*(perftest|unittest|ficus)' -type f |parallel rm -v {} # delete files with name matching regex
    find . -type f -regextype posix-extended -regex '.*\.(h|hpp|cpp|cxx)' # search for files with names matching regular expression
    find src -type f -regextype posix-extended -regex '.*\.(h|hpp|cpp|cxx)' | while read f; do ln -sfv /mnt/disk/hdu/$f /mnt/disk/jacksp/src_cpu/${f:6} ; done # symbol link all source files to another directory
    find . -maxdepth 1 -iname '*namepattern'

#### sed
A simple text processing and transforming tool, mostly for regular expression matching.


    # substitute substring
    $ echo "Pattern" | sed -r 's/pattern/target/gI' # -r for extended regular expression, s for substitute, g for global, I for case insensitive
    target
    $ sed -r -i 's/pattern/target/g' # s for substitute, g for global, i for inplace
    $ sed -r -i '2,$s/pattern/target/g' # s for substitute, g for global, i for inplace, only operate between line 2 and last line

    # extract substring with regular expression pattern
    $ echo "ljljlsfs pattern jljslfjsdl" | sed -r 's/^.*(pattern).*$/\1/g' # s for substitute, g for global, i for inplace, \1 for back referencing
    pattern

    ## advanced example
    $ echo "hello cruel world" | sed -r 's/(h.+o)(.+)(w.+d)/\1, \3/g' # "hello cruel world" -> "hello, world"
    hello, world
    # parse text: extract fields(date, error code, error code literal name)
    $ cat leaf_node_service_worker_ficus.ERROR |sed -r -n -e 's/(E[0-9]+)[^a-zZ-Z]+?(\S+[ch]pp:[0-9]+).*error code: (-?[0-9]+), (\w+)/\1,\2,\3,\4/pg' > date-error-name.csv
    E0919,retrieval_storage_client.cpp:93,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR
    E0919,retrieval_retrieval_service_3.cpp:241,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list retrieval error
    E0919,retrieval_retrieval_service_3.cpp:220,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list retrieval error, will retry in 1 seconds
    E0919,retrieval_storage_client.cpp:127,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR
    E0919,retrieval_retrieval_service_3.cpp:271,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list false track error
    E0919,retrieval_retrieval_service_3.cpp:222,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list false track repo error, will retry in 1 seconds
    E0919,retrieval_storage_client.cpp:93,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR
    E0919,retrieval_retrieval_service_3.cpp:241,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list retrieval error
    E0919,retrieval_retrieval_service_3.cpp:220,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list retrieval error, will retry in 1 seconds
    E0919,retrieval_storage_client.cpp:127,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR


- -r, --regexp-extended: use extended regular expression
- -i: inplace


#### awk
A versatile programming language.

Execution order

Refer to:
- man page `man awk`
- [tutorialspoint](https://www.tutorialspoint.com/awk/awk_workflow.htm)
- [linuxhandbook](https://linuxhandbook.com/awk-command-tutorial/)
- [An intro to the great language with the strange name](https://www.ibm.com/developerworks/library/l-awk1/index.html)

![image](./data/awk_workflow.jpg)


For each input file, if a BEGINFILE rule exists, gawk executes the associated code before processing
the contents of the file. Similarly, gawk executes the code associated with ENDFILE after processing the file.

For each RECORD in the input, gawk TESTS to see if it matches any PATTERN in the AWK program.
For each pattern that the record matches, gawk executes the associated action.
The patterns are tested in the order they occur in the program.

Finally, after all the input is exhausted, gawk executes the code in the END rule(s) (if any).


Variables
- RS: record separator
- FS: field separator
- NR: total Number of input Records seen so far, starting with 1. if RS is set to the empty string, then records are separated by sequences consisting of a `<newline>` plus one or more blank lines.
- `$n`: extract field, where n is a number starting with 1. `n=0` means the entire record.

Using arrays
All arrays in AWK are `ASSOCIATIVE ARRAYS`, so they allow associating an arbitrary string with another value

Examples

    # PRINT first and last field of each line, separated by ','
    $ cat input | awk '{print $1, $NF}'

    # FORMAT PRINT
    $ echo 1 2 | awk '{printf "input is %s and %s", $1, $2}'
    input is 1 and 2

    # REGULAR EXPRESSION MATCHING and array accumulate
    $ echo "input: 1;\ninput: 2;\ninput: 3;" |awk 'match($0, /input: ([^;]+)/, x){a[NR] += x[1]} END{printf "input is %s, %s, %s", a[1], a[2], a[3]}'
    $ echo "input: 1;\ninput: 2;\ninput: 3;" |awk '$0 ~ /input: ([^;]+)/{a[NR] += $2} END{printf "input is %s, %s, %s", a[1], a[2], a[3]}'
    $ echo "input: 1;\ninput: 2;\ninput: 3;" |awk '{if(match($0, /input: ([^;]+)/, x))a[NR] += x[1]} END{printf "input is %s, %s, %s", a[1], a[2], a[3]}'
    input is 1, 2, 3

    # CONDITIONAL STATEMENT: search for [zZ] pattern and filter duplicate
    $ awk '/[zZ]/ && !a[$2]++ {print $2}'
    # kill zombie process
    kill $(ps -A -ostat,ppid | awk '/[zZ]/ && !a[$2]++ {print $2}') # [zZ] for pattern, a[$2]++ to filter duplicate ppid.

    # access CAPTURED GROUP from line pattern
    $ echo "abcdefgh" | gawk 'match($0, /b(.*)e((f).+)/, a) {print a[1]"\t"a[2]}'
    cd    f
    # back reference
    $ echo abbc | awk '{ print gensub(/a(b*)c/, "Here are bees: \\1", "g", $1);}'
    Here are bees: bb

    # process a csv file, copy all files at the first field, and substitue destination name by replacing pattern with target
    $ cat feature.3030.csv|awk '{FS=","}NR > 1 {print $1}' |while read f
    do
        cp -v $f  /tmp/features/$(basename $f|sed -r 's/pattern/target/g')
    done

    # REPLACE string but SKIP first line with CONDITIONAL STATEMENT
    $ echo -e "This is first line.\nThis is PATTERN1. END" | awk 'NR==1{print}NR>1{sub(/PATTERN1/,"PATTERN2");print}'
    This is first line.
    This is PATTERN2. END

    # generate a tabular separated value file: prepend a header line, sort by columns 1 and 2 numerically
    # NOTE: sort will skip first header line.
    $ cat input.txt | awk 'BEGIN{print "col1\tcol2\tcol3\tcol4"} {print $1"\t"$2"\t"$3"\t"$4 | "sort -k 1,1n -k 2,2n"}'

    # SET operation
    # generate Cartesian product of two files
    $ awk 'NR==FNR {a[$0]; next}{for (i in a) print i"\t"$0}' file1.txt file2.txt

    # get elements in file 1 excluding elements in file 2
    $ awk 'NR==FNR {a[$0] = 1; next} a[$0] == 0 {print $0}' file2.xt file1.txt

    # join two files row wise
    awk 'NR==FNR {a[NR] = $0; next}{print a[FNR]"\t"$0}' file1.txt file2.txt

### sort

    $ cat input.txt
    3       tomato
    1       onion
    4       beet
    2       pepper
    2       apple

    $ cat input.txt | sort -k 1,1n -k 2,2h # sort by multiple columns
    2       apple
    2       pepper
    3       tomato
    4       beet
    10      onion

    $ cat input.txt | sort -k 1,1nr -k 2d,2 # column 1: numeric, reverse, column 2: dictionary

    10      onion
    4       beet
    3       tomato
    2       apple
    2       pepper

    $ cat input.txt | sort -k 1,1nr -k 2d,2r # column 1: numeric, reverse, column 2: dictionary, reverse
    10      onion
    4       beet
    3       tomato
    2       pepper
    2       apple

### uniq - report or omit repeated lines

It can be used to group or aggregate results.

    $ cat input.txt
    a
    c
    a
    c
    a
    b

    $ cat a.txt | sort |uniq -c  |sort -k1,1nr
    3 a
    2 b
    1 c

- -c, --count: prefix line by the number of occurrences


### eu-stack
TODO

Parallel processing
-------------------
- Use GNU/parallel or xargs command.
- Use wait built-in command with &.
- Use xargs command.

### background task with `&`

    prog1 &
    prog2 &
    wait
    prog3

###  `parallel`
Refer to `man parallel_tutorial`

    # use ::: to input data
    $ parallel --no-notice echo {} ::: A B C
    A
    B
    C

    # PIPE data into parallel
    $ echo -e 'a\nb\nc'  |parallel --no-notice echo processed {}
    processed a
    processed b
    processed c

    $ parallel echo {} ::: A B C ::: D E F
    A D
    A E
    A F
    B D
    B E
    B F
    C D
    C E
    C F

    # want to copy files parallely? rsync -R for relative to keep file hierarchy
    $ find src/ -not -path .git |parallel rsync -avPR {} dst/

- `{}` for replacement string(placeholder)

### `xargs`
Sequentially execute batch tasks.

    $ ls
    A B C
    $ find . -type f |xargs -I {} echo "Found {}"
    Found A
    Found B
    Found C
    $ find . -type f -exec echo 'Found {}' \;
    Found A
    Found B
    Found C
    $ # find . -type f |xargs -I {} sed -i -r 's/pattern/target/g' |awk ...

- `-I replace-str`: replace occurrences of string `replace-str` with names read from standard input. 

### `find`

    # https://stackoverflow.com/questions/602706/batch-renaming-files-with-bash
    find . -type f |sed -n -r 's/(.+)pattern(.+)/mv \1pattern\2 \1target\2/p' |sh # batch renaming multiple files


File system
------------

### `/proc/$PID/`

Refer to `man proc`

Experiment:
Run `deadloop` and experiment with those tools.

- `/proc/$PID/cmdline`: command line that started this process
- `/proc/$PID/exe`: `realpath /proc/$PID/exec` the program being run.
- `/proc/$PID/cwd`: link to current working directory
- `/proc/$PID/fd/`: directory of symbolic links to opened files
- `/proc/$PID/comm`: thread name, [`pthread_setname_np`](https://linux.die.net/man/3/pthread_setname_np) and `pthread_getname_np` will open `/proc/self/task/[tid]/comm`, .
- `/proc/$PID/task`: threads/tasks.
- `/proc/$PID/stat`: 14 system time, 15 user time, blah blah.. `pidstat` is an easier tool.
- `/proc/$PID/status`: VmSize for memory usage?
- `/proc/$PID/environ`: `cat /proc/37517/environ|tr '\0' '\n'` to display environment variables of a running process.
- `/proc/$PID/maps`: mapped memory regions

### `/var/log/auth.log` - system authentication log

For example, if someone used `sudo kill` to kill your process behind you, you can check it out there.


Static analysis tool
--------------------

### cppcheck

### clang-tools

Quality assurance tools
-----------------------

### [Sanitizers](https://github.com/google/sanitizers)

- ASan: Address Sanitizer detects use-after-free, buffer-overflow, and leaks.
- TSAN: Thread Sanitizer detects data races, deadlocks.
- MSAN: Memory Sanitizer detects uses of uninitialized memory.
- UBSan: Undefined Behavior Sanitizer detects… that

New tools, based on compiler instrumentation, ~2x slow down(https://www.usenix.org/sites/default/files/conference/protected-files/enigma_slides_serebryany.pdf).
Available in LLVM and GCC(with higher version>=6).

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
    =================================================================
    ==32182==ERROR: LeakSanitizer: detected memory leaks

    Direct leak of 7 byte(s) in 1 object(s) allocated from:
        #0 0x4b8af8  (/tmp/build/a.out+0x4b8af8)
        #1 0x4ece5a  (/tmp/build/a.out+0x4ece5a)
        #2 0x7f5bda8e182f  (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

    SUMMARY: AddressSanitizer: 7 byte(s) leaked in 1 allocation(s).

Use-after-free:

    /**
     * a.cpp
     */
    int main(int argc, char **argv) {
      int *array = new int[100];
      delete [] array;
      return array[argc]; 
    }

Compile with address sanitizer and run:

    clang++ -O0 -std=c++11 -fsanitize=address a.cpp && ./a.out
    =================================================================
    ==2565==ERROR: AddressSanitizer: heap-use-after-free on address 0x61400000fe44 at pc 0x0000004eced2 bp 0x7ffc4c3f7440 sp 0x7ffc4c3f7438
    READ of size 4 at 0x61400000fe44 thread T0
    #0 0x4eced1  (/tmp/build/a.out+0x4eced1)
    #1 0x7f0b31cfa82f  (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)
    #2 0x4189e8  (/tmp/build/a.out+0x4189e8)

    0x61400000fe44 is located 4 bytes inside of 400-byte region [0x61400000fe40,0x61400000ffd0)
    freed by thread T0 here:
    #0 0x4ea840  (/tmp/build/a.out+0x4ea840)
    #1 0x4ece86  (/tmp/build/a.out+0x4ece86)
    #2 0x7f0b31cfa82f  (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

    previously allocated by thread T0 here:
    #0 0x4ea240  (/tmp/build/a.out+0x4ea240)
    #1 0x4ece64  (/tmp/build/a.out+0x4ece64)
    #2 0x7f0b31cfa82f  (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

    SUMMARY: AddressSanitizer: heap-use-after-free (/tmp/build/a.out+0x4eced1)
    Shadow bytes around the buggy address:
    ...


#### How to check memory of a running process - Use gdb to call check function?

To use address sanitizer or leak sanitizer under `ptrace`(gdb, strace), we need to set:

    export LSAN_OPTIONS=detect_leaks=0

Then use gdb:

    gdb -p pid
    (gdb) break __sanitizer::Die
    (gdb) c
    (gdb) call __lsan_do_leak_check () # tips: tab can complete


The problem is, where did the output go?


#### Control flow sanitizer

    // a.c

    void Bad() { puts("BOOO"); }
    struct Expr {
     long a[2];
     long (*Op)(long *);
    };
    int main(int argc, char **argv) {
     struct Expr e;
     e.a[2 * argc] = (long)&Bad;
     e.Op(e.a);
    }

Compile and run:

    $ clang a.c && ./a.out
    BOOO
    $ clang -flto -fsanitize=cfi -fvisibility=hidden a.c && ./a.out
    Illegal instruction (core dumped)

#### Stack buffer overflow 

    // a.cpp
    void Bad() { puts("BOOO"); exit(0); }
    int main(int argc, char **argv) {
     long array[10];
     array[argc * 13] = (long)&Bad;
    }

Compile and run:

    % clang a.c && ./a.out
    BOOO
    % clang -fsanitize=safe-stack a.c && ./a.out
    [1]    10408 segmentation fault (core dumped)  ./a.out

### Set thread name

```cpp
    pthread_setname_np(pthread_self(), "thread_name");
```

### Testing

#### Unittest
- gtest

#### Fuzz testing(fuzzing/fuzzer)
- [libFuzzer](https://llvm.org/docs/LibFuzzer.html)

Shipped with `LLVM` compiler's `-fsanitizer` option.


Reference:
- https://llvm.org/docs/LibFuzzer.html
- https://github.com/google/fuzzer-test-suite/blob/master/tutorial/libFuzzerTutorial.md


Profiling tools
---------------


Gprof, Gcov, gperftools, perf_events

Reference:
[gprof, valgrind, gperftools](http://gernotklingler.com/blog/gprof-valgrind-gperftools-evaluation-tools-application-level-cpu-profiling-linux/), [perf_events](http://www.brendangregg.com/perf.html)

For large applications, heavy profiling tools isn't appropriate. Light-weighted tools like `perf_events` comes in handy.
One strategy is to use `perf_events` to draw statistics about most heavy low level system call, then override those
functions with `LD_PERLOAD` magic to get information of corresponding call stacks.

If you want to debug a specific module, profiling with manually inserted code to draw statistics of program execution
will be a good choice if external tools don't work.

### The USE(Utilization Saturation and Errors) Method

Reference: http://www.brendangregg.com/usemethod.html

### perf_event

#### Record cpu clock

    perf record -e cpu-clock --call-graph dwarf ./a.out # profile ./a.out by sampling with cpu-clock event 
    perf record -e cs --call-graph dwarf ./a.out # profile ./a.out by sampling with context switch event 
    perf report # report

#### Off-CPU analysis

Generic thread states
Performance issues can be categorized into one of two types:
- On-CPU: where threads are spending time running on-CPU.
- Off-CPU: where time is spent waiting while blocked on I/O, locks, timers, paging/swapping, etc.



    # echo 1 > /proc/sys/kernel/sched_schedstats # since Linux kernel 4.5
    # perf record -e sched:sched_stat_sleep -e sched:sched_switch \
        -e sched:sched_process_exit -a -g -o perf.data.raw sleep 1
    # perf inject -v -s -i perf.data.raw -o perf.data
    # perf script -f comm,pid,tid,cpu,time,period,event,ip,sym,dso,trace | awk '
        NF > 4 { exec = $1; period_ms = int($5 / 1000000) }
        NF > 1 && NF <= 4 && period_ms > 0 { print $2 }
        NF < 2 && period_ms > 0 { printf "%s\n%d\n\n", exec, period_ms }' | \
        ./stackcollapse.pl | \
        ./flamegraph.pl --countname=ms --title="Off-CPU Time Flame Graph" --colors=io > offcpu.svg

Reference:
- http://www.brendangregg.com/offcpuanalysis.html
- http://www.brendangregg.com/blog/2015-02-26/linux-perf-off-cpu-flame-graph.html
- https://github.com/iovisor/bcc#tracing

Note:
perf record for 

### eBPF - bcc tools

Reference:
http://www.brendangregg.com/blog/2019-01-01/learn-ebpf-tracing.html

### SystemTap

TODO

### [gperftools](https://github.com/gperftools/gperftools/wiki)
`gperftools` is a collection of high-performance multi-threaded `malloc` implementation, and performance analysis tools.
- Thread-caching(TC) malloc
- heap checker
- heap profiler
- cpu profiler 
- pprof and remote servers

#### Install

    sudo apt install --no-install-recommends libgoogle-perftools-dev google-perftools

#### TC malloc

Link the library:

    gcc [...] -ltcmalloc

Or inject code with `LD_PRELOAD`:

    export LD_PRELOAD=/usr/lib/libtcmalloc.so

#### Heap checker

    gcc [...] -o myprogram -ltcmalloc
    HEAPCHECK=normal ./myprogram
    pprof ./myprogram "/tmp/myprogram.308._main_-end.heap" --inuse_objects --lines --heapcheck  --edgefraction=1e-10 --nodefraction=1e-10  --text

Or inject code with `LD_PRELOAD`, like other following tools

    LD_PRELOAD=/usr/lib/libtcmalloc.so HEAPCHECK=normal ./myprogram

Explicit (Partial-program) Heap Leak Checking
Instead of whole-program checking, you can check certain parts of your code to verify they do not have memory leaks. 
This check verifies that between two parts of a program, no memory is allocated without being freed.

To use this kind of checking code, bracket the code you want checked by creating a `HeapLeakChecker` object at the beginning of the code segment, 
and call `NoLeaks()` at the end. These functions, and all others referred to in this file, are declared in `<gperftools/heap-checker.h>`.

Here's an example:

    HeapLeakChecker heap_checker("test_foo");
    {
      code that exercises some foo functionality;
      this code should not leak memory;
    }
    if (!heap_checker.NoLeaks()) assert(NULL == "heap memory leak");

Note that adding in the `HeapLeakChecker` object merely instruments the code for leak-checking. To actually 
turn on this leak-checking on a particular run of the executable, you must still run with the heap-checker turned on:

    $ env HEAPCHECK=local /usr/local/bin/my_binary_compiled_with_tcmalloc

If you want to do whole-program leak checking in addition to this manual leak checking, you can run in normal or
some other mode instead: they'll run the "local" checks in addition to the whole-program check.

#### Heap profiler

Link/inject the library and run the code:

    gcc [...] -o myprogram -ltcmalloc
    #HEAPPROFILE=/tmp/netheap ./myprogram
    HEAPPROFILE=/tmp/profile LD_PRELOAD=/usr/lib/libtcmalloc.so PPROF_PATH=/usr/bin/pprof ./bin/myprogram
    pprof ./myprogram "/tmp/profile.0001.heap" --inuse_objects --lines --heapcheck  --edgefraction=1e-10 --nodefraction=1e-10 --text

##### Call api

In your code, bracket the code you want profiled in calls to `HeapProfilerStart()` and `HeapProfilerStop()`.
(These functions are declared in `<gperftools/heap-profiler.h>`.)
`HeapProfilerStart()` will take the profile-filename-prefix as an argument.
Then, as often as you'd like before calling `HeapProfilerStop()`, you can use `HeapProfilerDump()` or GetHeapProfile() to examine the profile. 
In case it's useful, `IsHeapProfilerRunning()` will tell you whether you've already called `HeapProfilerStart()` or not.

Now that api is provided, we can attach a running process with gdb and call `HeapProfilerDump()` profile a snapshot.

    (gdb) attach $PID # attach to a running process
    (gdb) call HeapProfilerStart("/tmp/profile")
    (gdb) detach # detach from it
    ......
    (gdb) attach $PID
    (gdb) call HeapProfilerDump()
    (gdb) call HeapProfilerStop()

To use `gdb` with `LD_PRELAOD`:

    (gdb) set environment LD_PRELOAD /usr/lib/libprofiler.so # use set environment
    (gdb) set exec-wrapper env 'LD_PRELOAD=/usr/lib/libprofiler.so CPUPROFILE=/tmp/profile' # use exec-wrapper


#### Cpu Profiler

There are two alternatives to actually turn on CPU profiling for a given run of an executable:

Define the environment variable CPUPROFILE to the filename to dump the profile to. 
For instance, to profile `/usr/local/netscape`:

      gcc [...] -o myprogram -lprofiler
      $ CPUPROFILE=/tmp/profile /usr/local/netscape           # sh
      % setenv CPUPROFILE /tmp/profile; /usr/local/netscape   # csh

OR
In your code, bracket the code you want profiled in calls to `ProfilerStart()` and `ProfilerStop()`. 
(These functions are declared in `<gperftools/profiler.h>`).
`ProfilerStart()` will take the profile-filename as an argument.

To insert code with `LD_PRELOAD`:

    LD_PRELOAD=/usr/lib/libprofiler.so CPUPROFILE=/tmp/profile ./myprogram
    pprof --web ./bin/myprogram /tmp/profile

If `pprof` complains "No nodes to print", then the program uses CPU too little times.

#### Analyze dumped file with pprof
`gperftools heap profiler` will generate a heap profile output file. That file can be analyzed with with `pprof`. Some output example following cases above are given here.

Analyze heap checker output:

    $ pprof ./bin/deadloop "/tmp/deadloop.308._main_-end.heap" --inuse_objects --lines --heapcheck  --edgefraction=1e-10 --nodefraction=1e-10  --text
    Using local file ./bin/deadloop.
    Using local file /tmp/deadloop.23469._main_-end.heap.
    Total: 172 objects
      86  50.0%  50.0%       86  50.0% main /home/hdu/Documents/mine/dsa/language/cpp/deadloop.cpp:46
      86  50.0% 100.0%       86  50.0% main /home/hdu/Documents/mine/dsa/language/cpp/deadloop.cpp:48
       0   0.0% 100.0%      172 100.0% __libc_start_main /build/glibc-Cl5G7W/glibc-2.23/csu/../csu/libc-start.c:291
       0   0.0% 100.0%      172 100.0% _start ??:0

Analyze heap profiler output:

    $ pprof ./bin/deadloop "/tmp/profile.0001.heap" --inuse_objects --lines --heapcheck  --edgefraction=1e-10 --nodefraction=1e-10 --text
    Using local file ./bin/deadloop.
    Using local file /tmp/profile.0001.heap.
    Total: 379 objects
     189  49.9%  49.9%      189  49.9% main /home/hdu/Documents/mine/dsa/language/cpp/deadloop.cpp:46
     189  49.9%  99.7%      189  49.9% main /home/hdu/Documents/mine/dsa/language/cpp/deadloop.cpp:48
       1   0.3% 100.0%        1   0.3% __GI__IO_file_doallocate /build/glibc-Cl5G7W/glibc-2.23/libio/filedoalloc.c:127
       0   0.0% 100.0%        1   0.3% _IO_new_file_overflow /build/glibc-Cl5G7W/glibc-2.23/libio/fileops.c:820
       0   0.0% 100.0%        1   0.3% _IO_new_file_xsputn /build/glibc-Cl5G7W/glibc-2.23/libio/fileops.c:1331
       0   0.0% 100.0%        1   0.3% __GI__IO_doallocbuf /build/glibc-Cl5G7W/glibc-2.23/libio/genops.c:398
       0   0.0% 100.0%        1   0.3% __GI__IO_fwrite /build/glibc-Cl5G7W/glibc-2.23/libio/iofwrite.c:39
       0   0.0% 100.0%      379 100.0% __libc_start_main /build/glibc-Cl5G7W/glibc-2.23/csu/../csu/libc-start.c:291
       0   0.0% 100.0%      379 100.0% _start ??:0
       0   0.0% 100.0%        1   0.3% main /home/hdu/Documents/mine/dsa/language/cpp/deadloop.cpp:43
       0   0.0% 100.0%        1   0.3% std::__ostream_insert ??:0
       0   0.0% 100.0%        1   0.3% std::operator<<  ??:0

Analyze cpu profiler output:

    TODO

#### Best practice
Profiling the whole program may slow it down drastically. Consider profiling in a smaller granularity. 
- Call profiling API mannually in the program.
- Interact with the program with gdb to execute profiling API at appropriate time.
- Handle SINGPROF(man 7 signal) to deal trigger profiling.


### valgrind

  sudo apt install --no-install-recommends valgrind
  sudo apt install --no-install-recommends graphviz kcachegrind

This tools can debug memory errors(memory leak, bad access, segmentation fault...) and do other diagnostics.
But, it's 20x slow down, so use sanitizer where possible.

Reference: 
https://www.ibm.com/developerworks/community/blogs/6e6f6d1b-95c3-46df-8a26-b7efd8ee4b57/entry/detect_memory_leaks_with_memcheck_tool_provided_by_valgrind_part_i8?lang=en

#### common usage
```shell
valgrind ./executable # memory check
valgrind --leak-check=full # memory check
valgrind --track-origin=yes --leak-check=yes ./executable
valgrind --tool=callgrind ./executable # function and memory profiler
valgrind --tool=cachegrind --branch-sim=yes --cache-sim=yes bin/falseSharing # Cachegrind, a cache and branch-prediction profiler
valgrind --tool=drd --read-var-info=yes # drd(data race detection), a thread error detector
```

This seems to slow down the program significantly...

### git
We'll skip basic `git clone/commit/pull/push/commit/revert` usage.
Git commits have a TREE structure!

#### git rebase --onto
Refer to `git help rebase`.

       Assume the following history exists and the current branch is "topic":

                     A---B---C topic
                    /
               D---E---F---G master

       From this point, the result of either of the following commands:

           git rebase master
           git rebase master topic

       would be:

                             A'--B'--C' topic
                            /
               D---E---F---G master

       NOTE: The latter form is just a short-hand of git checkout topic followed by git rebase
       master. When rebase exits topic will remain the checked-out branch.


       Here is how you would transplant a topic branch based on one branch to another, to pretend
       that you forked the topic branch from the latter branch, using rebase --onto.

       First let's assume your topic is based on branch next. For example, a feature developed in
       topic depends on some functionality which is found in next.

               o---o---o---o---o  master
                    \
                     o---o---o---o---o  next
                                      \
                                       o---o---o  topic

       We want to make topic forked from branch master; for example, because the functionality on
       which topic depends was merged into the more stable master branch. We want our tree to look
       like this:

               o---o---o---o---o  master
                   |            \
                   |             o'--o'--o'  topic
                    \
                     o---o---o---o---o  next

       We can get this using the following command:

           git rebase --onto master next topic # transplate range from 'next' to 'topic' onto 'master'


#### git bisect


#### log 

#### FAQ
##### Valgrind on OSX reports false positive memory leak
ImageLoader is part of the OS X runtime and is responsible for loading binaries and dynamic libraries. It allocates some memory once, during initialization and forgets about it, but it's harmless because it's a small block of memory allocated only once. And it does a bunch of things that Valgrind doesn't like but that aren't incorrect.

Other ops tools
----------------

https://www.thegeekstuff.com/2011/12/linux-performance-monitoring-tools
https://www.tecmint.com/command-line-tools-to-monitor-linux-performance/

CPU    htop, top
GPU    gpu
process    ps, pstree
debug    gdb, ptrace(strace), perf, dtrace
memory    htop, free, pmap, vmstat
disk    df, du, iotop, iostat
network    nc, ping, iperf, iftop, nload, netstat, sar, tcpdump
misc    dstat, lsof, cat /proc

- htop
- [iftop](https://www.systutorials.com/docs/linux/man/8-iftop/)
- iotop
- nvidia-smi
- tcpdump


### netstat

    netstat -nlpte # list all listenig ports

- -n: numeric
- -l: listening
- -t: tcp
- -e: extend, display additional info

### lsof

    lsof -p $PID



production tools
-----------------
- mongodb
    - robo 3T

### Monitor tools

#### Grafana - analytics and monitoring
https://github.com/grafana/grafana

#### influxdb - time series database
time series database


