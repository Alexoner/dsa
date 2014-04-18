#ifndef RBTREE_H
#define RBTREE_H
/*****************************************
 * Red-Black tree implementation header file
 * ***************************************/
#include "../dsadef.h"
#include "btree.h"

/**
 *  A red-black tree is a binary search tree with one extra bit of storage per node:
 * its color, which can be either RED or BLACK . By constraining the node colors on any
 * simple path from the root to a leaf, red-black trees ensure that no such path is more
 * than twice as long as any other, so that the tree is approximately balanced.
 *
 * Each node of the tree now contains the attributes color, key, left, right, and p. If
 * a child or the parent of a node does not exist, the corresponding pointer attribute
 * of the node contains the value NIL . We shall regard these NIL s as being pointers to
 * leaves (external nodes) of the binary search tree and the normal, key-bearing nodes
 * as being internal nodes of the tree.
 *
 *  A red-black tree is a binary tree that satisfies the following red-black properties:
 *
 * 1. Every node is either red or black.
 * 2. The root is black.
 * 3. Every leaf ( NIL ) is black.
 * 4. If a node is red, then both its children are black.
 * 5. For each node, all simple paths from the node to descendant leaves contain the
 * same number of black nodes.
 *
 */

struct rbtree
{
    int color: 1;
#define RB_RED   0
#define RB_BLACK 1

    void *key;

    struct btree btree;
};

typedef struct rbtree RBtree;

#define rb_entry(ptr,type,member) container_of(ptr,type,member)
#define rb_btree_entry(ptr) container_of(ptr,struct rbtree,btree)

#define rb_parent(r) \
    rb_entry(r->btree.parent,struct rbtree,rbtree)
#define rb_left_child(r) \
    rb_entry(r->btree.left,struct rbtree,btree)
#define rb_right_child(r) \
    rb_entry(r->btree.right,struct rbtree,btree)

#define rb_color(r) ((r)->color)
#define rb_is_red(r) ((rb_color(r))==RB_RED)
#define rb_is_black(r) ((rb_color(r)) == RB_BLACK))
#define rb_set_red(r) do {rb_color(r) = RB_RED;} while(0)
#define rb_set_black(r) do {rb_color(r)= RB_BLACK;} while(0)


typedef btree_compare_t rb_compare_t;

#endif
