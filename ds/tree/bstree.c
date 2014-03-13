#include <stdlib.h>
#include "bstree.h"

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

Bstree *bstree_minimun(Bstree *x)
{
    while (x->left)
    {
        x = x->left;
    }
    return x;
}

Bstree *bstree_maximum(Bstree *x)
{
    return x;
}

Bstree *bstree_successor(Bstree *x)
{
    return x;
}

Bstree *bstree_predecessor(Bstree *x)
{
    return x;
}

Bstree *bstree_insert(Bstree *t, Bstree *x)
{
    return x;
}

Bstree *bstree_transplant(Bstree *t, Bstree *x)
{
    return x;
}

Bstree *bstree_delete(Bstree *t, Bstree *x)
{
    return x;
}


