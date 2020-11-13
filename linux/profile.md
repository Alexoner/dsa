Profiling tools
---------------

There are two kinds of profilers:
- Sampling based
- Event based (tracing, instrument)


Gprof, Gcov, gperftools, perf_events

Reference:
[gprof, valgrind, gperftools](http://gernotklingler.com/blog/gprof-valgrind-gperftools-evaluation-tools-application-level-cpu-profiling-linux/), [perf_events](http://www.brendangregg.com/perf.html)

For large applications, heavy profiling tools isn't appropriate. Light-weighted tools like `perf_events` comes in handy.
One strategy is to use `perf_events` to draw statistics about most heavy low level system call, then override those
functions with `LD_PERLOAD` magic to get information of corresponding call stacks.

If you want to debug a specific module, profiling with manually inserted code to draw statistics of program execution
will be a good choice if external tools don't work.

### perf_event
The USE(Utilization Saturation and Errors) Method: http://www.brendangregg.com/usemethod.html .

#### Record cpu clock

    perf record -e cpu-clock --call-graph dwarf ./a.out # profile ./a.out by sampling with cpu-clock event 
    perf record -e cs --call-graph dwarf ./a.out # profile ./a.out by sampling with context switch event 
    perf report # report

#### Off-CPU analysis

Generic thread states
Performance issues can be categorized into one of two types:
- On-CPU: where threads are spending time running on-CPU.
- Off-CPU: where time is spent waiting while blocked on I/O, locks, timers, paging/swapping, etc.


```shell
echo 1 > /proc/sys/kernel/sched_schedstats # since Linux kernel 4.5
perf record -e sched:sched_stat_sleep -e sched:sched_switch \
    -e sched:sched_process_exit -a -g -o perf.data.raw sleep 1
perf inject -v -s -i perf.data.raw -o perf.data
perf script -f comm,pid,tid,cpu,time,period,event,ip,sym,dso,trace | awk '
    NF > 4 { exec = $1; period_ms = int($5 / 1000000) }
    NF > 1 && NF <= 4 && period_ms > 0 { print $2 }
    NF < 2 && period_ms > 0 { printf "%s\n%d\n\n", exec, period_ms }' | \
    ./stackcollapse.pl | \
    ./flamegraph.pl --countname=ms --title="Off-CPU Time Flame Graph" --colors=io > offcpu.svg
```

Reference:
- http://www.brendangregg.com/offcpuanalysis.html
- http://www.brendangregg.com/blog/2015-02-26/linux-perf-off-cpu-flame-graph.html
- https://github.com/iovisor/bcc#tracing

Note:
Maybe kernel parameters need to be tuned.

### gprof
`gprof` uses a hybrid of instruments and sampling.


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


