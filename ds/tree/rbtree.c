#include "rbtree.h"

/**
 * Implementation is based on 'Introduction to Algorithms,Third Edition'
 * and Linux kernel
 */

/**
 * lemma 13.1:
 * A red-black tree with n internal nodes has height at most
 * 2lg(n + 1).
 */

struct rbtree *rbtree_search(struct rbtree *x,
                             struct rbtree *y,
                             rb_compare_t compare,
                             void *priv)
{
    return y;
}

struct rbtree *rbtree_search_recursion(struct rbtree *x,
                                       struct rbtree *y,
                                       rb_compare_t compare,
                                       void priv)
{
    return y;
}

struct rbtree *rbtree_minimum(struct rbtree *root)
{
    return root;
}

struct rbtree *rbtree_maximum(struct rbtree *root)
{
    return root;
}

struct rbtree *successor(struct rbtree *x)
{
    return x;
}

struct rbtree *predecessor(struct rbtree *x)
{
    return x;
}

int rbtree_left_rotate(struct rbtree *root, struct rbtree *x)
{
    return 0;
}

int rbtree_right_rotate(struct rbtree *root, struct rbtree *x)
{
    return 0;
}
