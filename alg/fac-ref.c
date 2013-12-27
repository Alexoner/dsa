#include <stdio.h>
#include <stdlib.h>

typedef struct node
{
    int data;
    struct node *prev,*next;
}Lnode,*Llist;//linked list

int main()
{
    Llist L,p,tail;//an extra pointer p can help reduce the times for judging "NULL" greatly! A tail can help locate the list better.
    int n,i,add;
    printf("please input the number n=\n");
    while(scanf("%d",&n))
    {
        tail=L=(Llist)malloc(sizeof(Lnode));
        L->data=1;
        L->prev=L->next=NULL;
        add=0;
        for(i=2;i<=n;i++)
        {
            for(p=L;p;p=p->next)
            {
                p->data=p->data*i+add;
                add=p->data/100000;
                p->data=p->data%100000;
                if(!p->next&&add)
                {
                    tail=(Llist)malloc(sizeof(Lnode));
                    tail->data=0;
                    tail->next=NULL;
                    tail->prev=p;
                    p->next=tail;
                }
            }
        }
        printf("%d",tail->data);
        p=tail;
        tail=tail->prev;
        free(p);
        while(tail)
        {
            printf("%d",tail->data);
            p=tail;//to avoid invalid pointer error
            tail=tail->prev;//to reassign tail,not using for loop;
            free(p);//when freeing a memory of a list,a index pointer is essential.
        }
        /*for(;tail;tail=tail->prev)
        {
            printf("%d",tail->data);
            free(tail->next);//tail->next maybe NULL;
        }*/
        printf("\nplease input a number\n");
    }
    return 0;
}





