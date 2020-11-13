Compiler
--------

    sudo apt install --no-install-recommends clang gcc-7

Debugger(ptrace), profiler
--------------------------


### objdump & readelf
These two commands are used to display information from object files.

	objdump -s ./a.out # -s --full-contents. display all sections
	objdump -d ./a.out # disassemble
	objdump -ds ./a.out # display both instructions and data.
	objdump -dj .text ./a.out # disassemble parts containing code
	objdump -sj .rodata ./a.out # display .rodata section
	readelf -x .rodata ./a.out # display .rodata section

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
    getconf PAGE_SIZE # get page size, usually 4096B=4KB

Note that `mprotect` needs the memory address to be page aligned.

#### `electric-fence`

    man libefence


