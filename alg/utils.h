#ifndef UTILS_H
#define UTILS_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define SWAP(x,y,type) \
    register type  __tmp = x; \
    x = y;               \
    y = __tmp;          \



static inline void * mem_swap(void *x, void *y, size_t size)
{
    void *p = malloc(size);
    if (p)
    {
        perror("mem_swap->malloc");
        return NULL;
    }
    memcpy(p, x, size);
    memcpy(x, y, size);
    memcpy(y, p, size);
    return x;
}

#endif

