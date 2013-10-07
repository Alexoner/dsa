/*************************************************************************
    > File Name: rand.c
    > Author: onerhao
    > Mail: haodu@hustunique.com
    > Created Time: 2013年10月07日 星期一 17时29分56秒
 ************************************************************************/

#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

struct randval
{
	int totaltimes;
	int currtimes;
};

struct list
{
	int *p;
	int *s;//Set s,needed when using multiple sets
	int size;//synchronous with currtimes
	int max_length;
};

struct list sc=
{
	NULL,0,0
};

struct randval rv=
{
	0,0
};

int s[]={1,2,3,4,5,6};

extern void quicksort(int *a,int p,int r);

int list_has(int *l,int n,int a);
int init_rands(struct list l,int n,struct randval rv,int m);
int free_rands_list(struct list l);
int rands_m(int *s,int n,int m);
int rands_m_gt(int *s,int n,int m,int a);
int rands_m_lt(int *s,int n,int m,int a);
int rands_lt(int *s,int n,int a);
int rands_gt(int *s,int n,int a);
int rand_lt(int a);


//check whether a list has this element
int list_has(int *l,int n,int a)
{
	int i;
	for(i=0;i<n;i++)
	{
		if(l[i]==a)
		{
			return 1;
		}
	}
	return 0;
}

int init_rands(struct list l,int n,struct randval rv,int m)
{//malloc n*sizeof(int) bytes memory for list
	l.p=malloc(sizeof(int)*n);
	if(!l.p)
	{
		return -1;
	}
	l.size=0;
	rv.totaltimes=m;
	rv.currtimes=0;
	return 0;
}

int free_rands_list(struct list l)
{
	if(l.p)
	{
		free(l.p);
		l.p=NULL;
	}
	return 0;
}

int rands_m(int *s,int n,int m)
{//generate no repeated random number within m times
	int i,j,k;
	if(m<=0||m>=n)
	{
		printf("Error: invalid m provided\n");
		return -1;
	}
	if(sc.p==NULL||sc.max_length<n)
	{
		sc.p=realloc(sc.p,n);
		if(!sc.p)
		{
			return -1;
		}
		sc.max_length=n;
		//rv.totaltimes=m;
	}
	if(rv.totaltimes!=m)
	{//reset and init
		rv.totaltimes=m;
		sc.size=rv.currtimes=0;
	}
	if(rv.currtimes==rv.totaltimes)
	{//every m times,reset  once
		rv.currtimes=0;
		sc.size=0;
	}
	i=rand_lt(n-rv.currtimes);
	for(j=0,k=0;j<n&&k<=i;j++)
	{
		if(list_has(sc.p,sc.size,j))
		{
			continue;
		}
		else
		{
			if(k==i)
			{
				break;
			}
			k++;
		}
	}
	if(j<n)
	{
		sc.size++;
		sc.p[sc.size-1]=j;
		rv.currtimes++;
	}
	return s[j];
}

int rands_m_gt(int *s,int n,int m,int a)
{//random without repeatition,and bigger than a in set s
	int i,pos,max_rand;
	quicksort(s,0,n-1);
	for(i=0;i<n;i++)
	{
		if(s[i]>a)
		{
			break;
		}
	}
	if(i>=n)
	{//no element bigger than a in set s
		return -1;
	}
	pos=i;
	max_rand=n-i;
	if(m>0&&m<max_rand)
		return rands_m(s+pos,max_rand,m);
	else
	{
		return -1;
	}
}

int rands_m_lt(int *s,int n,int m,int a)
{
	int i,pos,max_rand;
	quicksort(s,0,n-1);
	for(i=0;i<n;i++)
	{
		if(s[i]>a)
		{
			break;
		}
	}
	if(i<1)
	{
		return -1;
	}
	pos=i-1;
	max_rand=i-1;
	if(m>0&&m<max_rand)
	{
		return rands_m(s,max_rand,m);
	}
	return -1;
}

int rands_lt(int *s,int n,int a)
{
	int i,pos,max_rand,rand_num;
	quicksort(s,0,n-1);
	for(i=0;i<n;i++)
	{
		if(s[i]>a)
		{
			break;
		}
	}
	if(i<1)
	{
		return -1;
	}
	pos=i-1;
	max_rand=i-1;
	rand_num=rand_lt(max_rand);
	i=s[rand_num];
	return i;
}

int rands_gt(int *s,int n,int a)
{//generate random number bigger than a from set sorted set s
	int i,pos,max_rand,rand_num;
	quicksort(s,0,n-1);
	for(i=0;i<n;i++)
	{
		if(s[i]>a)
		{
			break;
		}
	}
	if(i>=n)
	{//no element bigger than a in set s
		return -1;
	}
	pos=i;
	max_rand=n-i;
	rand_num=rand_lt(max_rand);
	i=s[pos+rand_num];
	return i;
}

int rand_lt(int a)
{//return random number less than a
	int r;
	if(a<=0)
	{
		return -1;
	}
	//srand(time(NULL));
	r=rand();
	return r%a;
}

int main()
{
	int i;
	srand(time(NULL));
	/*for(i=0;i<6;i++)
	{
		printf("random is : %d\n",rands_m(s,6,4));
	}
	printf("\n");
	for(i=0;i<20;i++)
	{
		printf("random is: %d\n",rands_m(s,6,3));
	}
	printf("%d\n",rands_gt(s,6,2));*/
	for(i=0;i<10;i++)
	{
		printf("%d\n",rands_m_lt(s,6,3,5));
	}
	return 0;
}
