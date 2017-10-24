import socket
import os
import time

'''
Master worker processes model

Master process spawns and terminates worker processes.
Worker processes SHARE LISTENING SOCKET and do tasks in their run loops.

Inter-process communication can be achieved with sockets, shared memory, MPI and so on.
'''

def share_listening_socket():
    pids = []
    serversocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    serversocket.bind(("127.0.0.1", 8888))
    serversocket.listen(0)
    print("Listening on port %d" % 8888)

    # Child Process
    for i in range(10):
        pid = os.fork()
        if pid == 0:
            worker_loop("child%d" % (i + 1), serversocket)
        elif pid > 0:
            pids.append(pid)
            print("spawned child process %d with pid: %d" % (i + 1, pid))

    master_loop("parent", serversocket)

def worker_loop(message, s):
    tasks = []
    quit = False
    while not quit:
        c, addr = s.accept()
        print('Got connection from in %s' % message)
        tasks.append((c, addr))
        payload = c.recvmsg(1024)
        quit == (payload == 'quit')
        c.send(bytes('Thank you for your connecting to %s\n' % message, 'utf-8'))
        c.close()
    s.close()

def master_loop(message, s):
    while True:
        time.sleep(5)
        pass
    pass

if __name__ == "__main__":
    share_listening_socket()

