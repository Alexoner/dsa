
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


