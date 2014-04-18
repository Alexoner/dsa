#include "rbtree.h"

/**
 * Implementation is based on 'Introduction to Algorithms,Third Edition'
 * and Linux kernel
 */

/**
 *
 * We call the number of black nodes on any simple path from, but not including, a
 * node x down to a leaf the black-height of the node, denoted bh(x). By property 5,
 * the notion of black-height is well defined, since all descending simple paths from
 * the node have the same number of black nodes. We define the black-height of a
 * red-black tree to be the black-height of its root
 *
 * lemma 13.1:
 * A red-black tree with n internal nodes has height at most
 * 2lg(n + 1).
 */

struct btree *__rbtree_search(struct btree *x,
                              struct btree *y,
                              rb_compare_t compare,
                              void *priv)
{
    return __bstree_search(x, y, compare, priv);
}

/*struct btree *__rbtree_search_recursion(struct btree *x,*/
/*struct btree *y,*/
/*rb_compare_t compare,*/
/*void priv)*/
/*{*/
/*return __bstree_search_recursion(x, y, compare, priv);*/
/*}*/

struct btree *__rbtree_minimum(struct btree *root)
{
    return __bstree_minimum(root);
}

struct btree *__rbtree_maximum(struct btree *root)
{
    return __bstree_maximum(root);
}

struct btree *__successor(struct btree *x)
{
    return __bstree_successor(x);
}

struct btree *__predecessor(struct btree *x)
{
    return __bstree_predecessor(x);
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
 *              Y       <--------------         X
 *             / \      -------------->        / \
 *            X   γ     RIGHT-ROTATE(T,y)     α   Y
 *           / \                                 / \
 *          α   β                                β  γ
 */

struct rbtree *__rbtree_left_rotate(struct rbtree **root, struct rbtree *x)
{
    return rb_entry(__btree_left_rotate(&(*root->btree), x->btree),
                    struct rbtree, btree);
}

struct btree *__rbtree_right_rotate(struct btree **root, struct btree *x)
{
    return rb_entry(__btree_right_rotate(&(*root->btree), x->btree),
                    struct rbtree, btree);
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

struct rbtree *__rbtree_insert(struct rbtree *root,
                               struct rbtree *z,
                               rb_compare_t compare,
                               void *priv)
{
    /*struct rbtree **/
    bstree_insert(&root->btree, z->btree, compare, priv);
    z->btree.left = z->btree.right = NULL;
    z->color = RB_RED;

    __rbtree_insert_fixup(root, z);
    return z;
}

int __rbtree_insert_fixup(struct rbtree **root,
                          struct rbtree *z)
{
    struct btree *y = NULL;
    while (z->btree &&
            rb_color(rb_parent(z)) == RB_RED)
    {
        /*if (rb_parent(z) == rb_parent(rb_parent(z)))*/
        if (z->btree.parent == z->btree.parent->parent->left))
        {
            y = z->btree.parent->parent->right;
            if (rb_btree_entry(y)->color = RB_RED)           //case 1
            {
                rb_btree_entry(z.btree.parent)->color = RB_BLACK;
                rb_btree_entry(y)->color = RB_BLACK;
                rb_btree_entry(z->btree.parent->parent)->color = RB_RED;
                z = z->btree.parent->parent;
            }
            else
            {
                if (z == z->btree.parent->right)        //case 2
                {
                    z = z->btree.parent;
                    __rbtree_left_rotate(root, z);
                }
                rb_color(z->btree.parent) = RB_BLACK;       //case 3
                rb_color(z->btree.parent->parent) = RB_RED; //case 3
                __rbtree_right_rotate(root, rb_entry(z->btree.parent->parent));
            }
        }
        else
        {
            y = z->btree.parent->parent->left;
            if (rb_btree_entry(y)->color == RB_RED) //case 1
            {
                rb_btree_entry(z.btree.parent)->color = RB_BLACK;
                rb_btree_entry(y)->color = RB_BLACK;
                rb_btree_entry(z->btree.parent->parent)->color = RB_RED;
                z = z->btree.parent->parent;
            }
            else
            {
                if (z == z->btree.parent->right)    //case 2
                {
                    z = z->btree.parent;
                    __rbtree_left_rotate(root, z);
                }

                rb_entry(z->btree.parent)->color = RB_BLACK;
                rb_entry(z->btree.parent->parent)->color = RB_RED;
                __rbtree_right_rotate(root, rb_entry(z->btree.parent->parent));
            }
        }
    }

    (*root)->color = RB_BLACK;
    return 0;
}
