/**
 *
 * RUN:
 * $ mpirun -n 4 -hostfile host_file mpi_hello_world
 *
 * Examine mpi ports:
 * $ netstat -nlpte |grep mpi
 *
 * Examine mpi process:
 * $ ps aux | grep mpi
 *
 * Or, run with Horovod:
 * $ horovodrun -np 4 -H localhost:4 ./bin/mpi_hello_world
 */
#include <mpi.h>
#include <stdio.h>

/**
 * https://mpitutorial.com/tutorials/mpi-send-and-receive/
 */
int send_recv(int world_rank) {
    printf("BEGIN TESTING send, recv\n");
    int number;
    if (world_rank == 0) {
        number = -1;
        MPI_Send(&number, 1, MPI_INT, 1, 0, MPI_COMM_WORLD);
        printf("Process 0 sent number %d from process 0\n",
               number);
    } else if (world_rank == 1) {
        MPI_Recv(&number, 1, MPI_INT, 0, 0, MPI_COMM_WORLD,
                 MPI_STATUS_IGNORE);
        printf("Process 1 received number %d from process 0\n",
               number);
    }

    printf("END TESTING send, recv\n\n");
    return 0;
}

int ping_pong(int world_rank) {
    printf("BEGIN TESTING ping pong\n");
    int PING_PONG_LIMIT = 10;

    int ping_pong_count = 0;
    int partner_rank = (world_rank + 1) % 2;
    if (world_rank > 1) return 0; // only test between 0 and 1
    while (ping_pong_count < PING_PONG_LIMIT) {
        if (world_rank == ping_pong_count % 2) {
            // Increment the ping pong count before you send it
            ping_pong_count++;
            MPI_Send(&ping_pong_count, 1, MPI_INT, partner_rank, 0,
                     MPI_COMM_WORLD);
            printf("%d sent and incremented ping_pong_count "
                   "%d to %d\n", world_rank, ping_pong_count,
                   partner_rank);
        } else {
            MPI_Recv(&ping_pong_count, 1, MPI_INT, partner_rank, 0,
                     MPI_COMM_WORLD, MPI_STATUS_IGNORE);
            printf("%d received ping_pong_count %d from %d\n",
                   world_rank, ping_pong_count, partner_rank);
        }
    }
    printf("END TESTING ping pong\n\n");
    return 0;
}

int ring(int world_rank, int world_size) {
    printf("BEGIN TESTING ring\n");
    int token;
    if (world_rank != 0) {
        MPI_Recv(&token, 1, MPI_INT, world_rank - 1, 0,
                 MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        printf("Process %d received token %d from process %d\n",
               world_rank, token, world_rank - 1);
    } else {
        // Set the token's value if you are process 0
        token = -1;
    }
    MPI_Send(&token, 1, MPI_INT, (world_rank + 1) % world_size,
             0, MPI_COMM_WORLD);

    // Now process 0 can receive from the last process.
    if (world_rank == 0) {
        MPI_Recv(&token, 1, MPI_INT, world_size - 1, 0,
                 MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        printf("Process %d received token %d from process %d\n",
               world_rank, token, world_size - 1);
    }
    printf("END TESTING ring\n\n");
}

int main(int argc, char** argv) {
    // Initialize the MPI environment
    MPI_Init(NULL, NULL);

    // Get the number of processes
    int world_size;
    MPI_Comm_size(MPI_COMM_WORLD, &world_size);

    // Get the rank of the process
    int world_rank;
    MPI_Comm_rank(MPI_COMM_WORLD, &world_rank);

    // Get the name of the processor
    char processor_name[MPI_MAX_PROCESSOR_NAME];
    int name_len;
    MPI_Get_processor_name(processor_name, &name_len);

    // Print off a hello world message
    printf("Hello world from processor %s, rank %d out of %d processors\n",
           processor_name, world_rank, world_size);

    // test send, recv
    send_recv(world_rank);
    sleep(1);

    ping_pong(world_rank);
    sleep(1);

    ring(world_rank, world_size);
    sleep(1);

    /* printf("press any key to continue...\n"); */
    /* getchar(); */

    // Finalize the MPI environment.
    MPI_Finalize();
}
