#include <stdio.h>
#include "define.h"
#define left(x) (2*(i))
#define right(x) (2*(i)+1)
#define parent(x) ((i)/2)
void max_heapify(int *a,int i)//array and the node index
{//to maintain the property of the max_heap (tree)
	int l,r,largest,tmp;
	l=left(i);
	r=right(i);
	if(l<=heap_size&&a[l-1]>a[i-1])
		largest=l;
	else
		largest=i;
	if(r<=heap_size&&a[r-1]>a[largest-1])//to select the biggest number
		largest=r;
	if(largest!=i)
	{
		//swap(a+i,a+largest);
        tmp=*(a+i-1);
        *(a+i-1)=*(a+largest-1);
        *(a+largest-1)=tmp;
		max_heapify(a,largest);
	}
    printf("after max_heapify:\n");
    for(tmp=0;tmp<heap_size;tmp++)
        printf("%d ",a[tmp]);
    putchar('\n');
}

void build_max_heap(int *a)
{
	int i;
	for(i=heap_size/2;i;i--)
		max_heapify(a,i);
}

void heapsort(int *a)
{
	int i,tmp;
	build_max_heap(a);
    printf("after build\n");
    for(i=0;i<heap_size;i++)
        printf("%d ",a[i]);
    printf("\n");
	for(i=heap_size;i>1;i--)
	{
		tmp=a[i-1];
		a[i-1]=a[0];
		a[0]=tmp;
		heap_size--;
		max_heapify(a,1);
	}
}


