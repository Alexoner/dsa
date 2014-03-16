#ifndef RBTREE_H
#define RBTREE_H
/*****************************************
 * Red-Black tree implementation header file
 * ***************************************/
#include "../dsadef.h"
#include "btree.h"

struct rbtree
{
    int color: 1;
#define RB_RED   0
#define RB_BLACK 1

    void *key;

    struct btree btree;
};

typedef struct rbtree RBtree;

#define rb_parent(r)
#define rb_color(r)
#define rb_is_red(r)
#define rb_is_black(r)
#define rb_set_red(r) do {;} while(0)
#define rb_set_black(r) do {;} while(0)

#define rb_entry(ptr,type,member) container_of(ptr,type,member)

typedef int (*rb_compare_t)(struct rbtree *, struct rbtree *, void *);

#endif
