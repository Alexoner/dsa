#include <stdio.h>
#include <stdlib.h>
#include "define.h"
//#include "linkedlist.h"

int length;

int main()
{
    Llist list,p,q;//p is index pointer
    int n,i,j,add;//n!,index,...,...,list length
    printf("please input a number n=");
    while(scanf("%d",&n))
    {
        list=NULL;
        p=list;
        length=0;
        add=0;
        insert(&list,p,1);
        q=p;
        length++;
        for(i=2;i<=n;i++)
        {
            p=list;
            for(j=0;j<length;j++)
            {
                if(!list->next)
                    p=list;
                p->data=p->data*i+add;
                add=p->data/100000;
                p->data=p->data%100000;
                //add=p->data/100000;
                //p->data=p->data%100000;
                if(j==length-1&&add)
                {
                    insert(&list,p,0);
                    length++;
                }
                q=p;//for p is set to NULL;
                p=p->next;
            }
        }
        printf("the result is:\n");
        //show(q,length);
        show(q);
        destroy(&list);
        printf("please input a number.n=");
    }
    return 0;
}

