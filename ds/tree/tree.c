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
    struct tree *left, *right;
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
        CreatebiTree(&(*T)->left);
        printf("Enter the right child value of node %p\n", (*T)->data);
        CreatebiTree(&(*T)->right);
    }
    return *T;
}

Tree *pre_traverse_r(Tree *T, int (*visit)(Tree *))
{
    //recursion
    visit(T);
    if (T)
    {
        pre_traverse_r(T->left, visit);
        pre_traverse_r(T->right, visit);
    }
    return T;
}

Tree *pre_traverse_s(Tree *T, int (*visit)(Tree*))
{
    visit(T);
    stack[++top] = T;
    T = T->left;
    while (top >= 0 || T)
    {
        while (T)
        {
            //push
            visit(T);
            stack[++top] = T;
            T = T->left;
        }
        T = stack[top]->right; //push right child
        top--;//pop
    }
    top = -1;
    return T;
}

Tree *in_traverse_r(Tree *T, int (*visit)(Tree *))
{
    if (T)
        in_traverse_r(T->left, visit);
    visit(T);
    if (T)
        in_traverse_r(T->right, visit);
    return T;
}

Tree *in_traverse_s(Tree *T, int (*visit)(Tree *))
{
    stack[++top] = T;
    T = T->left;
    while (top >= 0 || T)
    {
        while (T)
        {
            //pushing is the same as preorder
            stack[++top] = T;
            T = T->left;
        }//left child into the stack
        visit(stack[top]);
        T = stack[top]->right;
        //maybe it's a root node with only right child

        top--;
    }
    top = -1;
    return T;
}

Tree *post_traverse_r(Tree *T, int (*visit)(Tree *))
{
    if (T)
    {
        post_traverse_r(T->left, visit);
        post_traverse_r(T->right, visit);
    }
    visit(T);
    return T;
}


Tree *post_traverse_s(Tree *T, int (*visit)(Tree *))
{
    stack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        //stop at empty stack
        while (T)
        {
            stack[++top] = T;
            T = T->left;
        }//push
        if (stack[top]->right)
        {
            //root node without left child
            T = stack[top]->right; //push right child tree
        }
        else
        {
            //leaf
            if (top >= 1 && stack[top - 1]->right == stack[top])
            {
                //right child visited,pop
                while (top >= 1 && stack[top - 1]->right == stack[top])
                {
                    visit(stack[top]);
                    top--;
                }           //if(top==0)
            }
            visit(stack[top]);
            top--;
            if (top >= 0)
                T = stack[top]->right;
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
    else if (!(T->left || T->right)) //a leaf
        return 1;
    else
        return leaf_numberr(T->left) + leaf_numberr(T->right);
}

int leaf_numbers(Tree *T)
{
    int result = 0;
    if (!T)
        return 0;
    stack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        while (T)
        {
            //push into stack
            stack[++top] = T;
            T = T->left;
        }
        if (!stack[top]->right)
        {
            //a leaf
            while (top >= 1 && stack[top - 1]->right == stack[top])
            {
                top--;
            }
            top--;
            result++;
        }
        if (top >= 0)
            T = stack[top]->right;
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
            stack[++top] = stack[bottom]->left;
            stack[++top] = stack[bottom]->right;
        }
        bottom++;
    }
    top = bottom = -1;
    return T;
}

int TreeHightr(Tree *T)
{
    int a, b;
    if (!(T && (T->left || T->right)))
        return 0;
    a = TreeHightr(T->left);
    b = TreeHightr(T->right);
    return (1 + ((a > b) ? a : b)); //watch the priority
}

int TreeHights(Tree *T)
{
    int result = 0, tmp = 0;
    stack[++top] = T;
    T = T->left;
    while (top >= 0)
    {
        while (T)
        {
            stack[++top] = T;
            tmp++;
            T = T->left;
        }//push
        //top--;
        //tmp--;
        if (!stack[top]->right)
        {
            //leaf
            if (tmp > result)
                result = tmp;
            if (top >= 1 && stack[top - 1]->right == stack[top])
            {
                while (top >= 1 && stack[top - 1]->right == stack[top])
                {
                    tmp--;
                    top--;//pop
                }
            }
            top--;
            tmp--;
        }
        if (top >= 0)
            T = stack[top]->right;
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
            pre_traverse_r(T, visit);
            break;
        case 3:
            pre_traverse_s(T, visit);
            break;
        case 4:
            in_traverse_r(T, visit);
            break;
        case 5:
            in_traverse_s(T, visit);
            break;
        case 6:
            post_traverse_r(T, visit);
            break;
        case 7:
            post_traverse_s(T, visit);
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

