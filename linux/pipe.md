### PIPE
Pipe operator `|` in linux shell is very powerful.
Another useful tool is NAMED PIPE(`man mkfifo`), which create a virtual file as a pipe in memory.

    cat input.txt |awk '{print $1}'
    mkfifo fifo # make a first in first out named pipe file
    echo "hello" > fifo # blocked, hang up
    cat fifo # both echo and cat finishes

    cat fifo # blocked, hang up
    echo "hello" > fifo # both echo and cat finishes


