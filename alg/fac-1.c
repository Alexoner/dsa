#include <stdio.h>
#include <stdlib.h>

struct node
{
   struct node *prev;
   int num;
   struct node *next;
};

int main(void)
{
   int i, n, a;
   struct node *p, *head , *tail;
   while(scanf("%d", &n))
   {
       head=(struct node*)malloc(sizeof(struct node));
       tail=head;
        head->num=1;
        head->next = head->prev = NULL;
        for (i=2; i<=n; i++)
        {    
            a=0;
            for (p=head; p!=NULL; p=p->next)
            {
                a+=p->num*i;
                p->num=a%1000000;
                a/=1000000;
                if (p->next==NULL && a!=0)
                {
                    tail = p->next = (struct node*)malloc(sizeof(struct node));
                    tail->num=a;
                    a=0;
                    tail->prev=p;
                    tail->next=NULL;
                    break;
                }
            }
        }
        printf("%d!=\n%d", n, (p=tail)->num);
        tail=p->prev;
        free(p);
        while (tail!=NULL)
        {
            printf("%06d ", tail->num);
            //printf("%d",tail->num);
            p=tail;
            tail=p->prev;
            free(p);
        }
        printf("\n");
    }
    return 0;
}
