#ifndef BTREE_H
#define BTREE_H
struct btree
{
    void *data;
    struct btree *parent;
    struct btree *left, *right;
};
typedef struct btree Btree;

#endif
