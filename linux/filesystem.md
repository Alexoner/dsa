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

### `/sys/devices/`

### `/sys/devices/system/cpu/cpu0/cache/`

- `/sys/devices/system/cpu/cpu0/cache/index0/coherency_line_size`: cache line/block size (bytes)
- `/sys/devices/system/cpu/cpu0/cache/index0/number_of_sets`: number of sets
- `/sys/devices/system/cpu/cpu0/cache/index0/ways_of_associativity`: ways of associativity
- `/sys/devices/system/cpu/cpu0/cache/index0/size`: size

```text
Rember that size = number of sets * ways of associativity * block size
Block Offset = Memory Address mod 2ⁿ
Block Address = Memory Address / 2ⁿ 
Set Index = Block Address mod 2^s
```


