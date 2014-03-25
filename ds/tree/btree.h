#ifndef BTREE_H
#define BTREE_H
struct btree
{
    void *data;
    struct btree *parent;
    struct btree *left, *right;
};
typedef struct btree Btree;
typedef int
(*btree_compare_t)(struct btree *, struct btree *, void *priv);

#endif
