// ex11_2.cpp : Defines the entry point for the console application.
//

//#include "stdafx.h"
/*input:
	a+b*(c-d)-e/f 
output:
L:2 op:1--- R:9
L:3 op:2--+ R:4
L:0 op:3--a R:0
L:5 op:4--* R:6
L:0 op:5--b R:0
L:7 op:6--- R:8
L:0 op:7--c R:0
L:0 op:8--d R:0
L:10 op:9--/ R:11
L:0 op:10--e R:0
L:0 op:11--f R:0
*/

#include "stdio.h"
#define MAXN 1000

int build_tree(char *s, int x, int y);
void preorder_traverse(int root);

int lch[MAXN],rch[MAXN];	//Ã¿žöœáµãµÄ×ó¶ù×Ó±àºÅºÍÓÒ¶ù×Ó±àºÅ
char op[MAXN];	//Ã¿žöœáµãµÄ×Ö·û
int nc=0,flag;	//œáµãÊý
char str[MAXN];

int main(void)
{
	char ch;
	int i=0,len,u;
	while((ch=getchar())!='\n')
	{
		flag=(ch>='a'&&ch<='z')||(ch>='A'&&ch<='Z')||(ch>='0'&&ch<='9')||(ch=='+')||(ch=='-')||(ch=='*')||(ch=='/')||(ch=='(')||(ch==')');
		if(flag)
		{
			str[i]=ch;
			i++;
		}
		else
		{
			printf("input error!\n");
			break;
		}
	}
	str[i]='\0';
	len=i;
	u=build_tree(str,0,len);
	preorder_traverse(u); 
	/*
	i=1;
	while(op[i]!='\0')
	{
		printf("L %c op %c R %c\n",str[lch[i]-1],op[i],str[rch[i]-1]);
		i++;
	}
	*/
	return 0;
}

void preorder_traverse(int root) /* ÏÈÐò±éÀú¶þ²æÊ÷ */
{
	  if(root!=NULL){
		  //printf("\t%p\t%p\t%d\t%p\n ",root,root->left,root->data,root->right);
		  //printf("L %c op %c R %c\n",str[lch[root]-1],op[root],str[rch[root]-1]);
		  printf("L:%d op:%d--%c R:%d\n",lch[root],root,op[root],rch[root]);
		  preorder_traverse(lch[root]);
		  preorder_traverse(rch[root]);
	  }
}

int build_tree(char *s, int x, int y)
{
	int i,c1=-1,c2=-1,p=0;
	int u;
	if(y-x==1)	//œöÒ»žö×Ö·û£¬œšÁ¢µ¥¶Àœáµã
	{
		u=++nc;
		lch[u]=rch[u]=0;
		op[u]=s[x];
		return u;
	}
	for(i=x;i<y;i++)
	{
		switch(s[i])
		{
		case '(': p++;break;
		case ')': p--;break;
		case '+':
		case '-': 
			if(!p) 
				c1=i;
			break;
		case '*':
		case '/':
			if(!p) 
				c2=i;
			break;
		}
	}
	if(c1<0)
		c1=c2;	//ÕÒ²»µœÀšºÅÍâµÄŒÓŒõºÅ£¬ŸÍÓÃ³Ë³ýºÅ
	if(c1<0)
		return build_tree(s,x+1,y-1);	//Õûžö±íŽïÊœ±»Ò»¶ÔÀšºÅÀšÆðÀŽ
	u=++nc;
	lch[u]=build_tree(s,x,c1);
	rch[u]=build_tree(s,c1+1,y);
	op[u]=s[c1];
	return u;
}
