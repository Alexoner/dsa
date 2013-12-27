#include <stdio.h>
#include <string.h>
#define  MAX 256

void infixtosufix(char *infix,char *sufix);
int compute(char *sufix);

int main()
{
    char infix[MAX],sufix[MAX],ch;
    int istrue;
    int t=0,i=0,flag=0;
    while(1)//stores the input into infix array
    {
        i=0;
        flag=0;
        while((ch=getchar())!='\n')
        {
            if(ch!='t'&&ch!='f'&&ch!='|'&&ch!='&'&&ch!='!'&&ch!='('&&ch!=')')
            {
                printf("input error\n");
                flag=1;
            }
            else
                infix[i++]=ch;
        }
        infix[i]='\0';
            t++;
            if(flag)
                break;
            if(!strlen(infix))
                break;
            infixtosufix(infix,sufix);
            istrue=compute(sufix);
            printf("espression %d\n",t);
            printf("%c\n",istrue?'T':'F');
    }
    return 0;
}

void infixtosufix(char *infix,char *sufix)
{//convert a infix expression into suffix one
    //char stk[MAX],ch;//stk is a stack
    char stk[MAX];
    char ch;
    int top,i,j;//top is the top of the stack
    i=j=0;//there must be a operator at last in the suffix expression
    top=-1;
    ch=infix[j++];
    while(ch!='\0')
    {
        if(ch==' ')
            ;//ignore space
        else if(ch=='(')
        {//parenthesis
            //stk[top++]=ch;
            top++;
            stk[top]=ch;
        }
        else if(ch==')')
		{
			while(stk[top]!='(')	/*将栈顶到字符“)”间的所有运算符依次出栈并插入到suffix的尾部*/
			{
				sufix[j]=stk[top];
				top--;
				j++;
			}
			top--;	/*字符“)”出栈*/
        }
        else if(ch=='|')
        {
            while(top!=-1&&stk[top]!='(')
            {//need to watch for parenthesis,for low priority
                sufix[i++]=stk[top--];
            }
            stk[++top]=ch;
        }
        else if(ch=='&')
        {
            while(stk[top]=='&'||stk[top]=='!')
            {
                sufix[i++]=stk[--top];
            }
            stk[++top]=ch;//into a stack
        }
        else if(ch=='!')
        {
            stk[++top]=ch;
        }
        else 
        {
            sufix[i++]=ch;
            while(top!=-1&&stk[top]=='!')
            {
                sufix[i++]=stk[top--];
            }
        }
        ch=infix[j++];
    }
   while(top!=-1)
    {
        sufix[i++]=stk[top--];
    }
    sufix[i]='\0';
}

int compute(char *sufix)
{
    int top=-1,i=0,stk[MAX];
    char ch;
    ch=sufix[i];
    while(ch!='\0')
    {
        if(ch=='t')
            stk[++top]=1;
        else if(ch=='f')
            stk[++top]=0;
        else if(ch=='|')
        {
            stk[top-1]=stk[top]||stk[top-1];
            top--;
            //stk[--top]=stk[top+1]||stk[top];
        }
        else if(ch=='&')
        {
            //stk[--top]=stk[top+1]&&stk[top];
            stk[top-1]=stk[top-1]&&stk[top];
            top--;
        }
        else if(ch=='!')
            stk[top]=!stk[top];
        ch=sufix[++i];
    }
    return stk[top];
}



