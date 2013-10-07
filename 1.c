#include "stdio.h"
#include "string.h"

const int MAX_STRLEN=256; /*逻辑表达式长度的最大值*/
const int MAX_STACKSIZE=256;	/*栈深度的最大值*/

void InfixToSuffix(const char * infix,char * suffix);
int Compute(const char *suffix);

int main(void)
{
	char infix[MAX_STRLEN],suffix[MAX_STRLEN],ch;
	int isTrue;
	int t=0,i=0;
	while(1)
	{
		i=0;
		while((ch=getchar())!='\n')
		{
			if(ch!='T'&&ch!='F'&&ch!='!'&&ch!='&'&&ch!='|'&&ch!='('&&ch!=')')	/*遇到不属于规定字符集的非法字符，结束*/
				goto DONE;
			infix[i]=ch;
			i++;
		}
		infix[i]='\0';

		if(strlen(infix)==0)
			break;
		t++;
		InfixToSuffix(infix,suffix);
		isTrue=Compute(suffix);
		printf("Expression %d: ",t);
		if(isTrue)
			printf("T\n");
		else
			printf("F\n");
	}
DONE:	return 0;
}

void InfixToSuffix(const char * infix,char * suffix)
{
	char stk[MAX_STACKSIZE];//a stack
	int top,i=0,j=0;//top is the top of the stack
	char ch;

	top=-1;
	ch=infix[i];
	i++;
	while(ch!='\0')
	{
		if(ch==' ')
			;			/*空格，不做任何处理*/
		else if(ch=='(')
		{
			top++;
			stk[top]=ch;	/*字符“(”入栈*/
		}
		else if(ch==')')
		{
			while(stk[top]!='(')	/*将栈顶到字符“)”间的所有运算符依次出栈并插入到suffix的尾部*/
			{
				suffix[j]=stk[top];
				top--;
				j++;
			}
			top--;	/*字符“)”出栈*/
		}
		else if(ch=='|')
		{
			while(top!=-1&&stk[top]!='(')/*将优先级不小于运算符“|”的所有运算符出栈并插入到suffix尾部*/
			{
				suffix[j]=stk[top];
				top--;
				j++;
			}
			top++;
			stk[top]=ch; /*运算符“|”入栈*/
		}
		else if(ch=='&')
		{
			while(stk[top]=='&'||stk[top]=='!')/*将优先级不小于运算符“&”的所有运算符出栈并插入到suffix尾部*/
			{
				suffix[j]=stk[top];
				top--;
				j++;
			}
			top++;
			stk[top]=ch; /*运算符“&”入栈*/
		}
		else if(ch=='!')
		{
			top++;
			stk[top]=ch; 
		}
		else
		{
			suffix[j]=ch;
			j++;	/*将ch插入到suffix的尾部*/
			/*将所有运算符“！”依次出栈并插入到suffix的尾部*/
			while(top!=-1&&stk[top]=='!')/*将优先级不小于运算符“|”的所有运算符出栈并插入到suffix尾部*/
			{
				suffix[j]=stk[top];
				top--;
				j++;
			}
		}
		ch=infix[i];
		i++;	/*处理infix下一个字符*/
	}
	while(top!=-1)
	{
		suffix[j]=stk[top];
		top--;
		j++;
	}
	suffix[j]='\0';
}

int Compute(const char *suffix)
{
	int stk[MAX_STACKSIZE];
	int top,i=0;
	char ch;

	top=-1;
	ch=suffix[i];
	i++;
	while(ch!='\0')
	{
		if(ch=='|')
		{
			stk[top-1]=stk[top-1]||stk[top];
			top--;
		}
		else if(ch=='&')
		{
			stk[top-1]=stk[top-1]&&stk[top];
			top--;
		}
		else if(ch=='!')
			stk[top]=!stk[top];
		else if(ch=='T')
		{
			top++;
			stk[top]=1;
		}
		else if(ch=='F')
		{
			top++;
			stk[top]=0;
		}
		ch=suffix[i];
		i++;
	}
	return stk[top];
}
