/*************************************************************************
    > File Name: tree.c
    > Author: hao
    > Mail: onerhao@gmail.com
    > Created Time: Thu 01 Nov 2012 11:29:15 PM CST
    r: RECURSION.s:STACK
 ************************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX 30
/**********************************************
 * Binary tree implementation
 * ******************************************/

/**
 * @1 Preorder,in-order,post-order traversing a tree are DEPTH-FIRST
 * algorithem,implemented with recurse ,or essentially,STACK,a first in last
 * out data structure(LIFO).In depth-first algorithm,we push nodes until no
 * more children are found.We use a pointer to tree's node to iterate in a
 * loop,update its value to its left child and right child
 *
 * @2 BREADTH-FIRST search is a algorithm must be implemented with QUEUE,a first
 * in first out(FIFO) list data structure
 * 1)push a node into queue
 * 2)from the first node in the queue to the last node in the queue,do this:
 *      visit it,push  all of its children into the queue and pop the node out
 *      till the queue is empty
 * 3)
 */

typedef struct tree
{
    void *data;
    struct tree *lchild, *rchild;
} Tree;

Tree *stack[MAX];
int top = -1, bottom = -1;

extern void treemenu();

Tree *CreatebiTree(Tree **T)
{
    int num;
    scanf("%d", &num);
    if (num == 0)
        *T = NULL;
    else
    {
        if (!(*T = (Tree*)malloc(sizeof(Tree))))
            return NULL;
        memset(*T, 0, sizeof(Tree));
        (*T)->data = (void*)num;
        printf("Enter the left child value of node %p\n", (*T)->data);
        CreatebiTree(&(*T)->lchild);
        printf("Enter the right child value of node %p\n", (*T)->data);
        CreatebiTree(&(*T)->rchild);
    }
    return *T;
}

Tree *PreTraverser(Tree *T, int (*visit)(Tree *))
{
    //recursion
    visit(T);
    if (T)
    {
        PreTraverser(T->lchild, visit);
        PreTraverser(T->rchild, visit);
    }
    return T;
}

Tree *PreTraverses(Tree *T, int (*visit)(Tree*))
{
    visit(T);
    stack[++top] = T;
    T = T->lchild;
    while (top >= 0 || T)
    {
        while (T)
        {
            //push
            visit(T);
            stack[++top] = T;
            T = T->lchild;
        }
        T = stack[top]->rchild; //push right child
        top--;//pop
    }
    top = -1;
    return T;
}

Tree *InTraverser(Tree *T, int (*visit)(Tree *))
{
    if (T)
        InTraverser(T->lchild, visit);
    visit(T);
    if (T)
        InTraverser(T->rchild, visit);
    return T;
}

Tree *InTraverses(Tree *T, int (*visit)(Tree *))
{
    stack[++top] = T;
    T = T->lchild;
    while (top >= 0 || T)
    {
        while (T)
        {
            //pushing is the same as preorder
            stack[++top] = T;
            T = T->lchild;
        }//left child into the stack
        visit(stack[top]);
        T = stack[top]->rchild;
        //maybe it's a root node with only right child

        top--;
    }
    top = -1;
    return T;
}

Tree *PostTraverser(Tree *T, int (*visit)(Tree *))
{
    if (T)
    {
        PostTraverser(T->lchild, visit);
        PostTraverser(T->rchild, visit);
    }
    visit(T);
    return T;
}


Tree *PostTraverses(Tree *T, int (*visit)(Tree *))
{
    stack[++top] = T;
    T = T->lchild;
    while (top >= 0)
    {
        //stop at empty stack
        while (T)
        {
            stack[++top] = T;
            T = T->lchild;
        }//push
        if (stack[top]->rchild)
        {
            //root node without left child
            T = stack[top]->rchild; //push right child tree
        }
        else
        {
            //leaf
            if (top >= 1 && stack[top - 1]->rchild == stack[top])
            {
                //right child visited,pop
                while (top >= 1 && stack[top - 1]->rchild == stack[top])
                {
                    visit(stack[top]);
                    top--;
                }           //if(top==0)
            }
            visit(stack[top]);
            top--;
            if (top >= 0)
                T = stack[top]->rchild;
        }
    }//while(top>=0)
    top = -1;
    return NULL;
}

int leaf_numberr(Tree *T)
{
    if (!T)
    {
        return 0;
    }
    else if (!(T->lchild || T->rchild)) //a leaf
        return 1;
    else
        return leaf_numberr(T->lchild) + leaf_numberr(T->rchild);
}

int leaf_numbers(Tree *T)
{
    int result = 0;
    if (!T)
        return 0;
    stack[++top] = T;
    T = T->lchild;
    while (top >= 0)
    {
        while (T)
        {
            //push into stack
            stack[++top] = T;
            T = T->lchild;
        }
        if (!stack[top]->rchild)
        {
            //a leaf
            while (top >= 1 && stack[top - 1]->rchild == stack[top])
            {
                top--;
            }
            top--;
            result++;
        }
        if (top >= 0)
            T = stack[top]->rchild;
        //top--;
    }
    return result;
}

Tree *Traverse(Tree *T, int (*visit)(Tree*))
{
    //breadth-first traversing a tree
    if (!T)
        return NULL;
    stack[++top] = T;
    bottom++;
    while (bottom <= top)
    {
        if (stack[bottom])
        {
            //a queue
            visit(stack[bottom]);
            stack[++top] = stack[bottom]->lchild;
            stack[++top] = stack[bottom]->rchild;
        }
        bottom++;
    }
    top = bottom = -1;
    return T;
}

int TreeHightr(Tree *T)
{
    int a, b;
    if (!(T && (T->lchild || T->rchild)))
        return 0;
    a = TreeHightr(T->lchild);
    b = TreeHightr(T->rchild);
    return (1 + ((a > b) ? a : b)); //watch the priority
}

int TreeHights(Tree *T)
{
    int result = 0, tmp = 0;
    stack[++top] = T;
    T = T->lchild;
    while (top >= 0)
    {
        while (T)
        {
            stack[++top] = T;
            tmp++;
            T = T->lchild;
        }//push
        //top--;
        //tmp--;
        if (!stack[top]->rchild)
        {
            //leaf
            if (tmp > result)
                result = tmp;
            if (top >= 1 && stack[top - 1]->rchild == stack[top])
            {
                while (top >= 1 && stack[top - 1]->rchild == stack[top])
                {
                    tmp--;
                    top--;//pop
                }
            }
            top--;
            tmp--;
        }
        if (top >= 0)
            T = stack[top]->rchild;
    }
    return result;
}


int visit(Tree *T)
{
    if (T)
        printf("%p ", T->data);
    return 1;
}

int main()
{
    Tree *T = NULL;
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
            CreatebiTree(&T);
            break;
        case 2:
            PreTraverser(T, visit);
            break;
        case 3:
            PreTraverses(T, visit);
            break;
        case 4:
            InTraverser(T, visit);
            break;
        case 5:
            InTraverses(T, visit);
            break;
        case 6:
            PostTraverser(T, visit);
            break;
        case 7:
            PostTraverses(T, visit);
            break;
        case 8:
            printf("The tree's leaves:%d\n", leaf_numberr(T));
            break;
        case 9:
            printf("The tree's leaves:%d\n", leaf_numbers(T));
            break;
        case 10:
            Traverse(T, visit);
            break;
        case 11:
            printf("Hight:%d\n", TreeHightr(T));
            break;
        case 12:
            printf("Hight:%d\n", TreeHights(T));
            break;
        default:
            break;
        }
        printf("\n************************************\n");
    }
    return 0;
}

