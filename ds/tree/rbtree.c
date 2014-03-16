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

/**
 * The search-tree operations TREE-INSERT and TREE-DELETE ,
 * when run on a red-black tree with n keys, take O(lgn) time.
 *
 * Because they modify the tree, the result may violate the
 * red-black properties enumerated in Section 13.1. To restore
 * these properties, we must change the colors of some of the
 * nodes in the tree and also change the pointer structure.
 *
 * We change the pointer structure through rotation, which is a
 * local operation in a search tree that preserves the
 * binary-search-tree property.
 *
 *              |       LEFT-ROTATE(T,x)        |
 *              Y       -------------->         X
 *             / \      <--------------        / \
 *            X   γ     RIGHT-ROTATE(T,y)     α   Y
 *           / \                                 / \
 *          α   β                                β  γ
 */

int rbtree_left_rotate(struct rbtree *root, struct rbtree *x)
{
    return 0;
}

int rbtree_right_rotate(struct rbtree *root, struct rbtree *x)
{
    return 0;
}

/**
 * We can insert a node into an n-node red-black tree in
 * O(lgn) time.
 *
 * To do so, we use a slightly modified version of the
 * TREE-INSERT procedure (Section 12.3,binary search tree) to
 * insert node z into the tree T as if it were an ordinary binary
 * search tree, and then we color z red.
 *
 * To guarantee that the red-black properties are preserved, we
 * then call an auxiliary procedure RB-INSERT-FIXUP to recolor
 * nodes and perform rotations. The call RB-INSERT(T,z) inserts
 * node z, whose key is assumed to have already been filled in,
 * into the red-black tree T.
 */
