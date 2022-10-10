# `/proc` file system

## inspect all processes, parent processes

    ps -ef

## Find process opened file

	ls /proc/{$PID}/fd -lhR
    (find /proc -type l | xargs ls -l | fgrep "$FILE") 2>/dev/null

## list open files by a process

    ls /proc/{$PID}/fd -lhR
	netstat -npte  # check socket status



## Example

	apt install procps net-tools iproute2

	ps -ef

	PID=28241

    # process trace
	strace -fp $PID -ttt  # strace program, find where it's stuck

    # process open files
	ls /proc/{$PID}/fd -lhR  # find out which file IO is stuck

	(find /proc -type l | xargs ls -l | fgrep "$FILE") 2>/dev/null

    # network
	netstat -npte  # check socket status
	cat /proc/net/tcp
