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

typedef int (*visit_t)(struct btree *, void *priv);

struct btree *btree_stacktack[MAX];
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

struct btree *__pre_traverse_recursion(struct btree *T,
                                       visit_t visit,
                                       void *priv)
{
    //recursion
    visit(T, priv);
    if (T)
    {
        __pre_traverse_recursion(T->left, visit, priv);
        __pre_traverse_recursion(T->right, visit, priv);
    }
    return T;
}

struct btree *__pre_traverse_stack(struct btree *T,
                                   visit_t visit,
                                   void *priv)
{
    visit(T, priv);
    btree_stacktack[++top] = T;
    T = T->left;
    while (top >= 0 || T)
    {
        while (T)
        {
            //push
            visit(T, priv);
            btree_stacktack[++top] = T;
            T = T->left;
        }
        T = btree_stacktack[top]->right; //push right child
        top--;//pop
    }
    top = -1;
    return T;
}

Bitree *pre_traverse(Bitree *t,
                     visit_t visit,
                     void *priv)
{
    return __pre_traverse_stack(t, visit, priv);
}

struct btree *__in_traverse_recursion(struct btree *T,
                                      visit_t visit,
                                      void *priv)
{
    if (T)
        __in_traverse_recursion(T->left, visit, priv);
    visit(T, priv);
    if (T)
        __in_traverse_recursion(T->right, visit, priv);
    return T;
}

struct btree *__in_traverse_stack(struct btree *T,
                                  visit_t visit,
                                  void *priv)
{
    btree_stacktack[++top] = T;
    T = T->left;
    while (top >= 0 || T)
    {
        while (T)
        {
            //pushing is the same as preorder
            btree_stacktack[++top] = T;
            T = T->left;
        }//left child into the stack
        visit(btree_stacktack[top], priv);
        T = btree_stacktack[top]->right;
        //maybe it's a root node with only right child

        top--;
    }
    top = -1;
    return T;
}

struct btree *__post_traverse_recursion(struct btree *T,
                                        visit_t visit,
                                        void *priv)
{
    if (T)
    {
        __post_traverse_recursion(T->left, visit, priv);
        __post_traverse_recursion(T->right, visit, priv);
    }
    visit(T, priv);
    return T;
}


struct btree *__post_traverse_stack(struct btree *T,
                                    visit_t visit,
                                    void *priv)
{
    btree_stacktack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        //stop at empty stack
        while (T)
        {
            btree_stacktack[++top] = T;
            T = T->left;
        }//push
        if (btree_stacktack[top]->right)
        {
            //root node without left child
            T = btree_stacktack[top]->right; //push right child tree
        }
        else
        {
            //leaf
            if (top >= 1 && btree_stacktack[top - 1]->right == btree_stacktack[top])
            {
                //right child visited,pop
                while (top >= 1 && btree_stacktack[top - 1]->right == btree_stacktack[top])
                {
                    visit(btree_stacktack[top], priv);
                    top--;
                }           //if(top==0)
            }
            visit(btree_stacktack[top], priv);
            top--;
            if (top >= 0)
                T = btree_stacktack[top]->right;
        }
    }//while(top>=0)
    top = -1;
    return NULL;
}

int __leaf_number_recursion(struct btree *T)
{
    if (!T)
    {
        return 0;
    }
    else if (!(T->left || T->right)) //a leaf
        return 1;
    else
        return __leaf_number_recursion(T->left) + __leaf_number_recursion(T->right);
}

int __leaf_number_stack(struct btree *T)
{
    int result = 0;
    if (!T)
        return 0;
    btree_stacktack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        while (T)
        {
            //push into stack
            btree_stacktack[++top] = T;
            T = T->left;
        }
        if (!btree_stacktack[top]->right)
        {
            //a leaf
            while (top >= 1 && btree_stacktack[top - 1]->right == btree_stacktack[top])
            {
                top--;
            }
            top--;
            result++;
        }
        if (top >= 0)
            T = btree_stacktack[top]->right;
        //top--;
    }
    return result;
}

struct btree *__traverse(struct btree *T,
                         visit_t visit,
                         void *priv)
{
    //breadth-first traversing a tree
    if (!T)
        return NULL;
    btree_stacktack[++top] = T;
    bottom++;
    while (bottom <= top)
    {
        if (btree_stacktack[bottom])
        {
            //a queue
            visit(btree_stacktack[bottom], priv);
            btree_stacktack[++top] = btree_stacktack[bottom]->left;
            btree_stacktack[++top] = btree_stacktack[bottom]->right;
        }
        bottom++;
    }
    top = bottom = -1;
    return T;
}

int __tree_height_recursion(struct btree *T)
{
    int a, b;
    if (!(T && (T->left || T->right)))
        return 0;
    a = __tree_height_recursion(T->left);
    b = __tree_height_recursion(T->right);
    return (1 + ((a > b) ? a : b)); //watch the priority
}

int __tree_height_stack(struct btree *T)
{
    int result = 0, tmp = 0;
    btree_stacktack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        while (T)
        {
            btree_stacktack[++top] = T;
            tmp++;
            T = T->left;
        }//push
        //top--;
        //tmp--;
        if (!btree_stacktack[top]->right)
        {
            //leaf
            if (tmp > result)
                result = tmp;
            if (top >= 1 && btree_stacktack[top - 1]->right == btree_stacktack[top])
            {
                while (top >= 1 && btree_stacktack[top - 1]->right == btree_stacktack[top])
                {
                    tmp--;
                    top--;//pop
                }
            }
            top--;
            tmp--;
        }
        if (top >= 0)
            T = btree_stacktack[top]->right;
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
            __pre_traverse_recursion(T, visit, NULL);
            break;
        case 3:
            __pre_traverse_stack(T, visit, NULL);
            break;
        case 4:
            __in_traverse_recursion(T, visit, NULL);
            break;
        case 5:
            __in_traverse_stack(T, visit, NULL);
            break;
        case 6:
            __post_traverse_recursion(T, visit, NULL);
            break;
        case 7:
            __post_traverse_stack(T, visit, NULL);
            break;
        case 8:
            printf("The tree's leaves:%d\n", __leaf_number_recursion(T));
            break;
        case 9:
            printf("The tree's leaves:%d\n", __leaf_number_stack(T));
            break;
        case 10:
            __traverse(T, visit, NULL);
            break;
        case 11:
            printf("Hight:%d\n", __tree_height_recursion(T));
            break;
        case 12:
            printf("Hight:%d\n", __tree_height_stack(T));
            break;
        default:
            break;
        }
        printf("\n************************************\n");
    }
    return 0;
}
