# gdb
Compile the binaries with debug symbols, and run it with gdb.

## Start gdb

    gdb [prog|prog procID|prog core]
    gdb program
    gdb program core
    gdb program pid
    gdb -p $PID

## Execute commands at startup

    gdb program --ex "run <--args>"

Or run a script:

```shell
#!/bin/sh
# file: debug

ARGS=${@:2}
gdb $1 -ex "${ARGS}"
```

## Essential commands and common practices

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
gdb> b __GI___libc_write if $rdi == 2 # set break point when writing to stderr(2), x86 register
gdb> b __GI___libc_write if $x0 == 2 # set break point when writing to stderr(2), ARM register
# https://stackoverflow.com/questions/23757996/gdb-how-to-break-on-something-is-written-to-cout
gdb> b fwrite if $rcx==&_IO_2_1_stdout_
gdb> b fwrite if $rcx==&_IO_2_1_stderr_ # Intel register
gdb> info break # list breakpoints
gdb> # watch [-l|-location] expr [thread thread-id] [mask maskvalue]. 
gdb> # Set a watchpoint for an expression
gdb> # In gdb there two types of watch points: hardware and software.
gdb> # Programmatic watch point? See debug registers.
gdb> watch foo
gdb> watch foo mask 0xffff00ff # watch variable address for bit mask
gdb> watch *0xdeadbeef mask 0xffffff00 # watch address for mask
gdb> watch -l *address # equivalent to watch -l pString._M_ptr
gdb> # Ordinarily a watchpoint respects the scope of variables in expr (see below). 
gdb> # The -location argument tells GDB to instead watch the memory referred to by expr
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
gdb> x $rbp+8 # examine return address of current call, on IA32
gdb> x /4xw $rip # examine memory pointed by $rip (instruction register), 4 words hex
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


## GUI

https://sourceware.org/gdb/wiki/GDB%20Front%20Ends

[gdbgui](https://github.com/cs01/gdbgui/) is awesome.

Refrence
- https://sourceware.org/gdb/onlinedocs/gdb/Assignment.html
- https://sourceware.org/gdb/onlinedocs/gdb/Compiling-and-Injecting-Code.html
- https://www.codeproject.com/Articles/33340/Code-Injection-into-Running-Linux-Application
- https://blogs.oracle.com/linux/8-gdb-tricks-you-should-know-v2

## Use scenarios

### [Dump all thread stack to a file](https://stackoverflow.com/questions/26805197/how-to-pipe-gdbs-full-stack-trace-to-a-file)
```shell
$ gdb <binary> core.dump
gdb> set logging on
gdb> set pagination off
gdb> thread apply all full bt
gdb> thread n # select thread n
gdb> f m # select frame depth with number m
```

### Modifying program state

```shell
gdb> call i = 0; # change variable i to 0
```
Abnormal program state and possible reasons
- Dirty data that doesn't make sense
    - Data race
    - Illegal memory access: object has been destroyed, so memory is used for other purpose.

### [Stack trace of running program](https://unix.stackexchange.com/questions/166541/how-to-know-where-a-program-is-stuck-in-linux)

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
call stack, which uses ptrace as underlying implementation.

### Generate core dump/exception for accessing a certain file - permission, blocking io
To get call stack for a process when accessing certain file, we can change the file's 
permission, or change the file to a named pipe blocking the reader or writer.

This is useful for debugging python system call.
