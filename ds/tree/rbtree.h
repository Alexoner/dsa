#ifndef RBTREE_H
#define RBTREE_H
/*****************************************
 * Red-Black tree implementation header file
 * ***************************************/
#include "btree.h"
#define RB_BLACK 0
#define RB_RED   0

struct rbtree
{
    int color: 1;

    struct btree btree;
};

typedef struct rbtree RBtree;

#endif
