# ptrace(strace & ltrace)

## manual

    man strace

## Usage

`strace` can be used to trace system call and signals.

    man strace
    strace -f $COMMAND
    strace -f -p $PID
    strace -fp $PID -Ttt -o app.strace # print out syscall
    strace -f -Ttt -e trace=%file -s 1024 ./a.out # trace file events of process a.out and its children processes. 1024 maximum lengto for argument data
    strace -w -c # show syscall latency

- `-f`: trace child processes, all threads
- `-e`/`--trace=`: value: %file, %network, or other function name
- -T: show time spent in system calls
- -t: prefix line with time of day
- -c/--summary: Count  time, calls, and errors for each system call and report a summary on program exit, suppressing the regular output
- -tt: macroseconds
- -o: output file

