#ifndef HASHTABLE_H
#define HASHTABLE_H
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//prototype for hash functions
typedef int (*hash_func_t)(int , int);

int chained_hash_insert(int *t, int x);
int chained_hash_search(int *t, int k);
int chained_hash_delete(int *t, int x);

static inline int  hash_interpret_string(char *s)
{
    int n = strlen((const char*)s), i;
    int key = 0;
    for (i = n; i; i--)
    {
        key = 128 * key + s[i - 1];
    }
    return key;
}

#endif








