# Linux debug troubleshooting tools

`GDB`, Strace, objdump, core dump, 

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

### linking & code injection with ld.so & ld

    man 8 ld.so
    man ld

#### LD_PRELOAD

#### ld --wrap=symbol

#### `mprotect`

#### `electric-fence`

    man libefence



