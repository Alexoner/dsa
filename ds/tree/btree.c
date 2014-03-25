/*************************************************************************
    > File Name: tree.c
    > Author: onerhao
    > Mail: onerhao@gmail.com
    > Created Time: Thu 01 Nov 2012 11:29:15 PM CST
 ************************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "btree.h"

#define MAX 30
/**********************************************
 * Binary tree implementation
 * ******************************************/

/**
 * @1 pre-order,in-order,post-order traversing a tree are DEPTH-FIRST
 * algorithem,implemented with RECURSION ,or essentially,STACK,a first in last
 * out data structure(LIFO).In depth-first algorithm,we push nodes until no
 * more children are found.We use a pointer to tree's node to iterate in a
 * loop,update its value to its left child and right child
 * r: RECURSION.s:STACK
 *
 * @2 BREADTH-FIRST search is a algorithm must be implemented with QUEUE,a first
 * in first out(FIFO) list data structure
 * 1)push a node into queue
 * 2)from the first node in the queue to the last node in the queue,do this:
 *      visit it,push  all of its children into the queue and pop the node out
 *      till the queue is empty
 * 3)
 */

typedef struct btree Bitree;


struct btree *btree_stack[MAX];
int top = -1, bottom = -1;

extern void treemenu();

Bitree *CreatebiBitree(Bitree **T)
{
    int num;
    scanf("%d", &num);
    if (num == 0)
        *T = NULL;
    else
    {
        if (!(*T = (Bitree*)malloc(sizeof(Bitree))))
            return NULL;
        memset(*T, 0, sizeof(Bitree));
        (*T)->data = (void*)num;
        printf("Enter the left child value of node %p\n", (*T)->data);
        CreatebiBitree(&(*T)->left);
        printf("Enter the right child value of node %p\n", (*T)->data);
        CreatebiBitree(&(*T)->right);
    }
    return *T;
}

struct btree *pre_traverse_r(struct btree *T, int (*visit)(struct btree *, void *priv),
                             void *priv)
{
    //recursion
    visit(T, priv);
    if (T)
    {
        pre_traverse_r(T->left, visit, priv);
        pre_traverse_r(T->right, visit, priv);
    }
    return T;
}

struct btree *pre_traverse_s(struct btree *T, int (*visit)(struct btree*, void *priv),
                             void *priv)
{
    visit(T, priv);
    btree_stack[++top] = T;
    T = T->left;
    while (top >= 0 || T)
    {
        while (T)
        {
            //push
            visit(T, priv);
            btree_stack[++top] = T;
            T = T->left;
        }
        T = btree_stack[top]->right; //push right child
        top--;//pop
    }
    top = -1;
    return T;
}

struct btree *in_traverse_r(struct btree *T, int (*visit)(struct btree *, void *priv),
                            void *priv)
{
    if (T)
        in_traverse_r(T->left, visit, priv);
    visit(T, priv);
    if (T)
        in_traverse_r(T->right, visit, priv);
    return T;
}

struct btree *in_traverse_s(struct btree *T, int (*visit)(struct btree *, void *priv),
                            void *priv)
{
    btree_stack[++top] = T;
    T = T->left;
    while (top >= 0 || T)
    {
        while (T)
        {
            //pushing is the same as preorder
            btree_stack[++top] = T;
            T = T->left;
        }//left child into the stack
        visit(btree_stack[top], priv);
        T = btree_stack[top]->right;
        //maybe it's a root node with only right child

        top--;
    }
    top = -1;
    return T;
}

struct btree *post_traverse_r(struct btree *T, int (*visit)(struct btree *, void *priv), void *priv)
{
    if (T)
    {
        post_traverse_r(T->left, visit, priv);
        post_traverse_r(T->right, visit, priv);
    }
    visit(T, priv);
    return T;
}


struct btree *post_traverse_s(struct btree *T, int (*visit)(struct btree *, void *priv),
                              void *priv)
{
    btree_stack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        //stop at empty stack
        while (T)
        {
            btree_stack[++top] = T;
            T = T->left;
        }//push
        if (btree_stack[top]->right)
        {
            //root node without left child
            T = btree_stack[top]->right; //push right child tree
        }
        else
        {
            //leaf
            if (top >= 1 && btree_stack[top - 1]->right == btree_stack[top])
            {
                //right child visited,pop
                while (top >= 1 && btree_stack[top - 1]->right == btree_stack[top])
                {
                    visit(btree_stack[top], priv);
                    top--;
                }           //if(top==0)
            }
            visit(btree_stack[top], priv);
            top--;
            if (top >= 0)
                T = btree_stack[top]->right;
        }
    }//while(top>=0)
    top = -1;
    return NULL;
}

int leaf_number_r(struct btree *T)
{
    if (!T)
    {
        return 0;
    }
    else if (!(T->left || T->right)) //a leaf
        return 1;
    else
        return leaf_number_r(T->left) + leaf_number_r(T->right);
}

int leaf_number_s(struct btree *T)
{
    int result = 0;
    if (!T)
        return 0;
    btree_stack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        while (T)
        {
            //push into stack
            btree_stack[++top] = T;
            T = T->left;
        }
        if (!btree_stack[top]->right)
        {
            //a leaf
            while (top >= 1 && btree_stack[top - 1]->right == btree_stack[top])
            {
                top--;
            }
            top--;
            result++;
        }
        if (top >= 0)
            T = btree_stack[top]->right;
        //top--;
    }
    return result;
}

struct btree *Traverse(struct btree *T, int (*visit)(struct btree*, void *priv),
                       void *priv)
{
    //breadth-first traversing a tree
    if (!T)
        return NULL;
    btree_stack[++top] = T;
    bottom++;
    while (bottom <= top)
    {
        if (btree_stack[bottom])
        {
            //a queue
            visit(btree_stack[bottom], priv);
            btree_stack[++top] = btree_stack[bottom]->left;
            btree_stack[++top] = btree_stack[bottom]->right;
        }
        bottom++;
    }
    top = bottom = -1;
    return T;
}

int tree_height_r(struct btree *T)
{
    int a, b;
    if (!(T && (T->left || T->right)))
        return 0;
    a = tree_height_r(T->left);
    b = tree_height_r(T->right);
    return (1 + ((a > b) ? a : b)); //watch the priority
}

int tree_height_s(struct btree *T)
{
    int result = 0, tmp = 0;
    btree_stack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        while (T)
        {
            btree_stack[++top] = T;
            tmp++;
            T = T->left;
        }//push
        //top--;
        //tmp--;
        if (!btree_stack[top]->right)
        {
            //leaf
            if (tmp > result)
                result = tmp;
            if (top >= 1 && btree_stack[top - 1]->right == btree_stack[top])
            {
                while (top >= 1 && btree_stack[top - 1]->right == btree_stack[top])
                {
                    tmp--;
                    top--;//pop
                }
            }
            top--;
            tmp--;
        }
        if (top >= 0)
            T = btree_stack[top]->right;
    }
    return result;
}


int visit(struct btree *T, void *priv)
{
    if (T)
        printf("%p ", T->data);
    return 1;
}

/**
 * Binary tree manipulation
 */

int main()
{
    struct btree *T = NULL;
    char option[20];
    while (1)
    {
        treemenu();
        scanf("%6s", option);
        if (!strcmp(option, "exit"))
            break;
        switch (atoi(option))
        {
        case 1:
            printf("Please enter the root node\n");
            CreatebiBitree(&T);
            break;
        case 2:
            pre_traverse_r(T, visit, NULL);
            break;
        case 3:
            pre_traverse_s(T, visit, NULL);
            break;
        case 4:
            in_traverse_r(T, visit, NULL);
            break;
        case 5:
            in_traverse_s(T, visit, NULL);
            break;
        case 6:
            post_traverse_r(T, visit, NULL);
            break;
        case 7:
            post_traverse_s(T, visit, NULL);
            break;
        case 8:
            printf("The tree's leaves:%d\n", leaf_number_r(T));
            break;
        case 9:
            printf("The tree's leaves:%d\n", leaf_number_s(T));
            break;
        case 10:
            Traverse(T, visit, NULL);
            break;
        case 11:
            printf("Hight:%d\n", tree_height_r(T));
            break;
        case 12:
            printf("Hight:%d\n", tree_height_s(T));
            break;
        default:
            break;
        }
        printf("\n************************************\n");
    }
    return 0;
}
