# Pipeline
In Unix-like computer operating systems, a **pipeline** is a mechanism for inter-process communication using message passing.
A pipeline is a set of processes chained together by their standard streams, so that the output text of each process (stdout) is passed directly as input (stdin) to the next one. 

The standard shell syntax for anonymous pipes is to list multiple commands, separated by vertical bars `|` ("pipes" in common Unix verbiage):

    process1 | process2 | process3
    cat input.txt |awk '{print $1}'
    mkfifo fifo # make a first in first out named pipe file
    echo "hello" > fifo # blocked, hang up
    cat fifo # both echo and cat finishes

    cat fifo # blocked, hang up
    echo "hello" > fifo # both echo and cat finishes

Another useful tool is NAMED PIPE(`man mkfifo`), which create a virtual file as a pipe in memory.

## status code
To get status code from previous command in the pipeline:

    echo ${PIPESTATUS{0]})}
    # or use pipefail shell option for bash
    set -o pipefail; false |tee /dev/null; echo $?
    bash -c 'set -o pipefail; command-not-existing |tee /dev/null'; echo $?

## Pipemil
The shell connects a series of sub-processes via pipes, and executes external commands within each sub-process.
This can be performed using a so-called *mill* or *pipemill*(since a `while` is used to "mill" over the resutls from the initial command).

	command | while read -r var1 var2 ...; do
	    # process each line, using variables as parsed into var1, var2, etc
	    # (note that this may be a subshell: var1, var2 etc will not be available
	    # after the while loop terminates; some shells, such as zsh and newer
	    # versions of Korn shell, process the commands to the left of the pipe
	    # operator in a subshell)
	done | parallel echo "processing {}" # can also be piped later for parallel processing

## Creating pipelines programmatically
The Unix `pipe()` system call asks the operating system to construct a new anonymous pipe object. This results in two new, opened file descriptors in the process: the read-only end of the pipe, and the write-only end. The pipe ends appear to be normal, anonymous file descriptors, except that they have no ability to seek.
`Named pipes` may also be created using `mkfifo()` or `mknod()` and then presented as the input or output file to programs as they are invoked. They allow multi-path pipes to be created, and are especially effective when combined with *standard error redirection*, or with `tee`.

## Network pipes
Tools like `netcat` and `socat` can connect pipes to TCP/IP sockets.
