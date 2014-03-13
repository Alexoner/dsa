#include <stdlib.h>
#include "bstree.h"

/**
 */
Bstree *bstree_search(Bstree *x,
                      Bstree *y,
                      int (*compare)(Bstree *, Bstree *, void *priv),
                      void *priv)
{
    if ( !x || !compare(x, y, priv))
    {
        return x;
    }
    else if (compare(x, y, priv) < 0 && x->right)
    {
        return bstree_search(x->right, y, compare, priv);
    }
    else
    {
        return bstree_search(x->left, y, compare, priv);
    }
}

Bstree *bstree_search_iteration(Bstree *x,
                                Bstree *y,
                                int (*compare)(Bstree *, Bstree *, void *prvi),
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

Bstree *bstree_minimum(Bstree *x)
{
    while (x->left)
    {
        x = x->left;
    }
    return x;
}

Bstree *bstree_maximum(Bstree *x)
{
    while (x->right)
    {
        x = x->right;
    }
    return x;
}

Bstree *bstree_successor(Bstree *x)
{
    Bstree *y;
    if ( x->right )
    {
        return bstree_minimum(x->right);
    }
    y = x->parent;
    while (y && x == y->right)
    {
        x = y;
        y = x->parent;
    }
    return y;
}

Bstree *bstree_predecessor(Bstree *x)
{
    Bstree *y = NULL;
    if (x->left)
    {
        return bstree_maximum(x->left);
    }
    y = x->parent;
    while (y && y->left == x)
    {
        x = y;
        y = x->parent;
    }
    return y;
}

Bstree *bstree_insert(Bstree **root, Bstree *z,
                      int (compare)(Bstree *, Bstree *, void *priv),
                      void *priv)
{
    Bstree *x = *root, *y = NULL;
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

Bstree *bstree_transplant(Bstree **root, Bstree *u, Bstree *v)
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

Bstree *bstree_delete(Bstree **root, Bstree *z)
{
    Bstree *y;
    if (z->left == NULL)
    {
        bstree_transplant(root, z, z->right);
    }
    else if (z->right == NULL)
    {
        bstree_transplant(root, z, z->left);
    }
    else
    {
        y = bstree_minimum(*root);
        if (y->parent != z)
        {
            bstree_transplant(root, y, y->right);
            y->right = z->right;
            y->right->parent = y;
        }
        bstree_transplant(root, z, y);
        y->left = z->left;
        z->left->parent = y;
    }
    return y;
}
