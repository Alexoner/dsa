### ps & top & htop

`ps`:
- -T: show threads
- -e: select all process
- -f: full format
- -F: extra full format
- -p: select by pid list

```shell
    ps aux # all processes
    ps -TFe # list all threads, with extra full format of all processes
    ps -TF -p $PID # list all threads, with extra full format, of process $PID
    ps -ef   # show pid, ppid,
    ps -efL  # show thread information
    # a zombie process is already dead, but not waited by parent process. Kill its parent will let 'init' process take over
    kill $(ps -A -ostat,ppid | awk '/[zZ]/ && !a[$2]++ {print $2}') # [zZ] for pattern, a[$2]++ to filter duplicate ppid.
```

#### memory

Sort processes by memory consumption

    ps aux |sort -k 4,4 -h -r |head
    ps aux -T --sort=-%mem |less
    top -H -p pid # only show process with pid and kernel process(cloned process, thread)
    htop -p pid

