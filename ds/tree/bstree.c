#include <stdlib.h>
#include "bstree.h"

typedef btree_compare_t bstree_compare_t;

/**
 */
struct btree *__bstree_search_recursion(struct btree *x,
                                        struct btree *y,
                                        bstree_compare_t compare,
                                        void *priv)
{
    if ( !x || !compare(x, y, priv))
    {
        return x;
    }
    else if (compare(x, y, priv) < 0 && x->right)
    {
        return __bstree_search_recursion(x->right, y, compare, priv);
    }
    else
    {
        return __bstree_search_recursion(x->left, y, compare, priv);
    }
}

struct btree *__bstree_search_iteration(struct btree *x,
                                        struct btree *y,
                                        bstree_compare_t compare,
                                        void *priv)
{
    while (x)
    {
        if (compare(x, y, priv) < 0 && x->right)
            x = x->right;
        else if (compare(x, y, priv) > 0 && x->left)
            x = x->left;
        else
            return x;
    }
    return NULL;
}

Bstree *bstree_search(Bstree *x,
                      Bstree *y,
                      bstree_compare_t compare,
                      void *priv)
{
    return __bstree_search_iteration(x, y, compare, priv);
}

struct btree *__bstree_minimum(struct btree *x)
{
    while (x->left)
    {
        x = x->left;
    }
    return x;
}

Bstree *bstree_minimum(Bstree *x)
{
    return __bstree_minimum(x);
}

struct btree *__bstree_maximum(struct btree *x)
{
    while (x->right)
    {
        x = x->right;
    }
    return x;
}

Bstree *bstree_maximum(Bstree *x)
{
    return __bstree_maximum(x);
}

struct btree *__bstree_successor(struct btree *x)
{
    struct btree *y;
    if ( x->right )
    {
        return __bstree_minimum(x->right);
    }
    y = x->parent;
    while (y && x == y->right)
    {
        x = y;
        y = x->parent;
    }
    return y;
}

Bstree *bstree_successor(Bstree *x)
{
    return __bstree_successor(x);
}

struct btree *__bstree_predecessor(struct btree *x)
{
    struct btree *y = NULL;
    if (x->left)
    {
        return __bstree_maximum(x->left);
    }
    y = x->parent;
    while (y && y->left == x)
    {
        x = y;
        y = x->parent;
    }
    return y;
}

Bstree *bstree_predecessor(Bstree *x)
{
    return __bstree_predecessor(x);
}

struct btree *__bstree_insert(struct btree **root,
                              struct btree *z,
                              btree_compare_t compare,
                              void *priv)
{
    struct btree *x = *root, *y = NULL;
    while (x)
    {
        y = x;
        if (compare(x, z, priv) < 0)
            x = x->right;
        else
            x = x->left;
    }
    z->parent = y;
    if (y == NULL)
    {
        *root = y;
    }
    else if (compare(y, z, priv) < 0)
    {
        y->right = z;
    }
    else
    {
        y->left = z;
    }
    return x;
}

Bstree *bstree_insert(Bstree **root,
                      Bstree *z,
                      bstree_compare_t compare,
                      void *priv)
{
    return __bstree_insert(root, z, compare, priv);
}

struct btree *__bstree_transplant(struct btree **root,
                                  struct btree *u, struct btree *v)
{
    if (u->parent == NULL)
    {
        *root = v;
    }
    else if (u == u->parent->left )
    {
        u->parent->left = v ;
    }
    else
    {
        u->parent->right = v;
    }
    if (v != NULL)
    {
        v->parent = u->parent;
    }
    return v;
}

Bstree *bstree_transplant(Bstree **root, Bstree *u, Bstree *v)
{
    return __bstree_transplant(root, u, v);
}

struct btree *__bstree_delete(struct btree **root, struct btree *z)
{
    struct btree *y = NULL;
    if (z->left == NULL)
    {
        __bstree_transplant(root, z, z->right);
    }
    else if (z->right == NULL)
    {
        __bstree_transplant(root, z, z->left);
    }
    else
    {
        y = __bstree_minimum(*root);
        if (y->parent != z)
        {
            __bstree_transplant(root, y, y->right);
            y->right = z->right;
            y->right->parent = y;
        }
        __bstree_transplant(root, z, y);
        y->left = z->left;
        z->left->parent = y;
    }
    return y;
}

Bstree *bstree_delete(Bstree **root, Bstree *z)
{
    return __bstree_delete(root, z);
}
