"""
MPI allreduce computation, with Horovod.

Execution:
$ horovodrun -np 10 -H localhost:10 python ../mpi/ex_allreduce.py

"""
#  import horovod.keras as hvd
import horovod.tensorflow.keras as hvd
import numpy as np

hvd.init()
world = hvd.size()
rank = int(hvd.rank())

D = 100
assert D % world == 0, "world size should be divisible by 100."
rows = D // world

print(f"Each worker computes {rows}/{D} rows.")
test_array = np.random.rand(D, D, D)  # DxDxD
# broadcast the original matrix
test_array = hvd.broadcast(test_array, 0, "test array")

# each process compute a small part of something and then compute the average etc.
# compute a small part
x = np.mean(test_array[rank*rows:(rank+1)*(rows),:,:])
# groud truth
y_bar = np.mean(test_array)

# compute the average for all processes, with all reduce, op=average
y = hvd.allreduce(x)  # reduce variable, aggregated to all nodes

# assess
loss = abs(y_bar - y)
assert loss < 1e-6, f"Exptect{y_bar}, got {y}, difference: {loss}"
#  if(rank==0):  #only one process print out the result
print(f"Rank: {rank}, mean of the big array is {y}, expect {y_bar}.")
