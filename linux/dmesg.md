### dmesg
If a process is killed by the process, likely because of OOM(out of memory). 

Then messages like this is expected in `dmesg |tail -n 20`

    [2901452.813490] Out of memory: Kill process 28345 (deadloop) score 765 or sacrifice child
    [2901452.813515] Killed process 28345 (deadloop) total-vm:21474908536kB, anon-rss:30564396kB, file-rss:4kB, shmem-rss:0kB
    [2901454.892452] oom_reaper: reaped process 28345 (deadloop), now anon-rss:0kB, file-rss:0kB, shmem-rss:0kB 

