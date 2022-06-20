# MPI for parallel computing inter-process communication

## Install OpenMPI

```shell
sudo apt install openmpi-bin
```

## Install Horovod

```shell
pip install tensorflow
HOROVOD_WITH_MPI=1 HOROVOD_WITH_TENSORFLOW=1 pip install --no-cache-dir horovod
```

## Reference

- https://mpitutorial.com/tutorials/mpi-hello-world/
