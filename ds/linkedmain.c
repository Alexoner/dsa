#include "linkedlist.h"
#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#define OFFSET offsetof(struct llist,next)

struct llist
{
    int a;
    struct llist *next;
};

int equal(void *x,void *y)
{
    return (*(int*)(x)==*(int*)(y));
}

int display(void*p)
{
    printf("%d ",*(int*)(p+offsetof(struct llist,a)));
    return 1;
}


int main()
{
    int op=0;
    struct llist *L=NULL,*p=NULL,*q=NULL,*node;
    node=(struct llist*)malloc(sizeof(struct llist));
    node->next=NULL;
    ListLoad((void**)&L,sizeof(struct llist),OFFSET,
            "linkedlist.dat");
    do
    {
        printf("\n\n");
        printf("      Menu for Linear Table On linked Structure \n");
        printf("------------------------------------------------------\n");
        printf("          1. InitiaList       7. LocateElem\n");
        printf("          2. DestroyList     8. PriorElem\n");
        printf("          3. ClearList       9. NextElem \n");
        printf("          4. ListEmpty      10. ListInsert\n");
        printf("          5. ListLength     11. ListDelete\n");
        printf("          6. GetElem        12. ListTrabverse\n");
        printf("          0. Exit\n");
        printf("------------------------------------------------------\n");

        printf("          Please input your option[0-12]:");
        scanf("%d",&op);
        getchar();
        switch(op)
        {
        case 0:
            ListSave(L,sizeof(struct llist),OFFSET,"linkedlist.dat");
            break;
        case 1:printf("\n     here is IntiaList(),which  being realized\n");
             ListInit((void**)&L,OFFSET);
             break;
        case 2:printf("\n     here is DestroyList(),which  being realized\n");
            ListDestroy((void**)&L,OFFSET);
            break;
        case 3:printf("\n     here is ClearList(),which  being realized\n");
             //ClearList(&L);
             break;
        case 4:
               printf("\n     here is ListEmpty(),which  being realized\n");
               printf("List is %s\n",ListEmpty(L,
                        offsetof(struct llist,next))?"empty":"not empty");
            break;
        case 5:printf("\n     here is ListLength() ,which  being realized\n");
             printf("The list length:%d\n",ListLength(L,offsetof(struct llist,next)));
             break;
        case 6:printf("\n     here is GetNode(),which  being realized\n please enter which element to find");
             break;
        case 7:printf("\n     here is LocateNode(),which  being realized\n");
             printf("what element's value do you want to inquire?\n");
             scanf("%d",&node->a);
             getchar();
             q=ListLocateNode(L,node,equal,OFFSET);
             if(q)
                 printf("element found: %d\n",q->a);
             break;
        case 8:
             printf("\n     here is PriorNode(),which  being realized\n");
             scanf("%d",&node->a);
             p=ListLocateNode(L,node,equal,offsetof(struct llist,next));
             p=ListPriorNode(L,p,offsetof(struct llist,next));
             if(p)
                 printf("The prior node is: %d\n",p->a);
             else
                 printf("Not found\n");
             break;
        case 9:
             printf("\n     here is NextNode(),which  being realized\n");
            scanf("%d",&node->a);
            getchar();
            p=ListLocateNode(L,node,equal,offsetof(struct llist,next));
            p=ListNextNode(L,p,offsetof(struct llist,next));
            if(p)
                printf("The next element is: %d\n",q->a);
            else
                printf("Not found\n");
            break;
        case 10:
            q=(struct llist*)malloc(sizeof(struct llist));
            q->next=NULL;
            printf("\n     here is ListInsert(),which  being realized\n");
            if(L)
            {
                printf("insert the element to append after\n");
                scanf("%d",&q->a);
                p=ListLocateNode((void*)L,q,equal,OFFSET);
                if(!p)
                    break;
            }
            else
                p=L;
            printf("Enter the element to insert \n");
            scanf("%d",&q->a);
            ListInsertAfter((void**)&L,p,q,OFFSET);
            ListTraverse(L,display,OFFSET);
            break;
        case 11:
            printf("\n     here is ListDelete(),which  being realized\n");
            scanf("%d",&node->a);
            getchar();
            p=ListLocateNode(L,node,equal,OFFSET);
            if(p)
            {
                ListDeleteNode((void**)&L,p,OFFSET);
            }
            break;
        case 12:
                printf("\n     here is ListTraverse(),which  being realized\n");
                 //char tablename[9];
                // getchar();
                ListTraverse(L,display,OFFSET);
                break;
        default:;
        }
    }while(op);
    printf("\n--------------------Welcome again!--------------------\n");
    return 0;
}

