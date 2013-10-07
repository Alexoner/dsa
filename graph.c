/*************************************************************************
    > File Name: graph.c
    > Author: hao
    > Mail: onerhao@gmail.com
    > Created Time: Tue 25 Dec 2012 07:41:28 PM CST
 ************************************************************************/
/* depth-first traversal
 * two methods: recursive and non-recursive
 * Graph is stored in an adjacency matrix
 */
#include<stdio.h>
#include<stdlib.h>

#define MAX     10

int sp = 0;//stack pointer
int stack[MAX];

/**********************stack***************************/
void push(int f)
{
    if(sp < MAX)
        stack[sp++] = f;
    else
        printf("error: stack full, can't push %d\n", f);
}

int pop(void)
{
    if(sp > 0)
        return stack[--sp];
    else {
        printf("error: stack empty\n");
        return 0;
    }
}


void buildGraph(int adj[][MAX], int n)
{
    int i, j;
    for(i=0; i<n; i++)
        for(j=0; j<n; j++)
        {
            printf("Enter 1 if there is an edge from %d to %d", i, j);
            scanf("%d", &adj[i][j]);
        }
}

/* depth-first traverse, start from node x by using recursive method*/
void dfs(int x, int visited[], int adj[][MAX], int n)
{
    int j;
    visited[x] = 1;
    printf("visit node %d\n", x);
    for(j=0; j<n; j++)
    {
        if(adj[x][j] == 1 && visited[j] == 0)
        {
            //visited[j] = 1;
            dfs(j, visited, adj, n);
        }
    }
}

/* depth-first traverse, start from node x by using non-recursive method */
/* method: put node visited into stack, and find new node not visited*/
void dfs_stack(int x, int visited[], int adj[][MAX], int n)
{
    int i, j;
    int node;
    int count = 1;
    printf("visit node %d\n", x);
    visited[x] = 1;
    node = x;
    push(x); //开始的节点入栈
    while(count < n) //still has node not visited
    {
    /* 所有被访问的节点依次入栈，只有node当找不到下一个相连的节点时，才使用出栈节点 */
        for(j=0; j<n; j++)
        {
            if(adj[node][j] == 1 && visited[j] == 0)
            {
                visited[j] = 1;
                printf("visit node %d\n", j);
                count++;
                push(j); //push node j
                break;
            }
        }
        if(j == n) //与node相连的节点都已经被访问过，所以需要从stack里取出node的上一个节点，再看该节点是否有相连的节点未被访问
            node = pop();
        else      //找到与node相连并且未被访问的节点，
            node = j;
    }
}

main(void)
{
    int adj[MAX][MAX] = {{0, 1, 1, 0, 1},
                         {1, 0, 0, 1, 0},
                         {1, 0, 0, 1, 0},
                         {0, 1, 1, 0, 0},
                         {1, 0, 0, 0, 0}
                        };

    int n = 5;
    char start_node;
    int visited[MAX];
    memset(visited, 0, MAX*sizeof(int));
    //printf("Enter number of nodes in graph: " );
    //scanf("%d", &n);
    //buildGraph(adj, n);

    printf("Depth-first traverse, enter the starting node: ");
    while((start_node = getchar()) != EOF)
    {
        getchar();
        memset(visited, 0, MAX*sizeof(int));
        printf("recursive: \n");
        dfs((int)atoi(&start_node), visited, adj, n);
        memset(visited, 0, MAX*sizeof(int));
        printf("non-recursive: \n");
        sp = 0;//此处也要将栈指针清0
        dfs_stack((int)atoi(&start_node), visited, adj, n);
    }
}

