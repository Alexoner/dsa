#include <stdio.h>//dynamic sequence list
#include <stdlib.h>
#define MAX 10

typedef struct //type define
{
    int *elem;//the elements of the sequence list
    int length;
    int listsize;//listsize to be MAX
}Sqlist;//sequence list

void initSqlist(Sqlist *L)
{
    L->elem=(int *)malloc(MAX*sizeof(int));//
    if(!L->elem)
        exit(0);
    L->length=0;
    L->listsize=MAX;
}

void delelem(Sqlist *L,int i)
{
    int *ptr,*q;
    if(i<1||i>L->length)
    {
        printf("error!out of range\n");
        exit(0);
    }
    else
    {
        q=L->elem+L->length-1;//the last element's address
        for(ptr=L->elem+i-1;ptr<q;ptr++)
            *ptr=*(ptr+1);
      //  free(L->elem+L->length-1);
        L->length--;
    }
}

void insertelem(Sqlist *L,int i,int item)
{
    int *base,*insertptr,*p;//p is the sentinel
    if(i<1||i>L->length+1)
    {
        printf("out of range\n");
        exit(0);
    }
    else
    {
        base=(int *)realloc(L->elem,(L->length+1)*sizeof(int));
        L->elem=base;
        p=L->elem+i-1;
        for(insertptr=L->elem+L->length-1;insertptr>=p;insertptr--)
            *(insertptr+1)=*insertptr;
        *p=item;
        L->length++;
    }
    printf("success in inserting\n");
}

int main()
{
    Sqlist l;
    int i,n,del,item;
    initSqlist(&l);
    printf("how many numbers you want to input?n=\n");
    if(!scanf("%d",&n))
            exit(0);
    printf("please input %d numbers\n",n);
    for(i=0;i<n;i++)
    {
        scanf("%d",&item);
        insertelem(&l,i+1,item);//insert some elements
    }
    printf("these are the originala numbers:\n");
    for(i=0;i<n;i++)
        printf("%d ",l.elem[i]);
    printf("now which element do you want to delete\n");
    if(!scanf("%d",&del))
        exit(0);
    delelem(&l,del);
    printf("the new seqence list is :\n");
    for(i=0;i<n-1;i++)
        printf("%d ",l.elem[i]);
    printf("\n");
    return 0;
}


