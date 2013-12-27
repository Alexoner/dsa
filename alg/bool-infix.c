#include <stdio.h>
#define MAX 256

int compute(char *infix);
int main()
{
    char infix[MAX],ch;
    int i,res,t;
    t=0;
    while(1)
    {
        i=0;
        ch=getchar();
        while(ch!='\n')
        {
            if(ch!='&'&&ch!='|'&&ch!='!'&&ch!='f'&&ch!='t'&&ch!='('&&ch!=')')
            {
                printf("error input \n");
                break;
            }
            infix[i++]=ch;
            ch=getchar();
        }
        infix[i]='\0';
        res=compute(infix);
        t++;
        printf("the %d expression:%c\n",t,res?'T':'F');
    }
    return 0;
}

int compute(char *infix)
{
    int operd[MAX],opert[MAX];
    int topd,topt,i;
    topd=topt=-1;
    char ch;
    i=0;
    while((ch=infix[i++])!='\0')
    {
        if(ch=='f')
            operd[++topd]=0;
        else if(ch=='t')
            operd[++topd]=1;
        else
        {
            if(topt==-1)
            {
                opert[++topt]=ch;
            }
            else
            {
                switch(ch)
                {
                    case '!':
                        while(topt!=-1&&opert[topt]=='!')
                        {
                            operd[topd]=!operd[topd];
                            topt--;
                        }
                        opert[++topt]=ch;
                        break;
                    case '&':
                        while(opert[topt]=='&'||opert[topt]=='|')
                        {
                            if(opert[topt]=='&')
                            {
                                operd[topd-1]=operd[topd-1]&&operd[topd];
                                topd--;
                            }
                            else
                            {
                                operd[topd]=!operd[topd];
                            }
                            topt--;
                        }
                        opert[++topt]=ch;
                        break;
                    case '|':
                        while(opert[topt]!='('&&topt!=-1)
                        {
                            if(opert[topt]=='&')
                            {
                                operd[topd-1]=operd[topd-1]&&operd[topd];
                                topd--;
                            }
                            if(opert[topt]=='|')
                            {
                                operd[topd-1]=operd[topd-1]||operd[topd];
                                topd--;
                            }
                            topt--;
                        }
                        opert[++topt]=ch;
                        break;
                    case '(':
                        opert[++topt]=ch;
                        break;
                    case ')':
                        while(opert[topt]!='(')
                        {
                            if(opert[topt]=='!')
                                operd[topd]=!operd[topd];
                            if(opert[topt]=='&')
                            {
                                operd[topd-1]=operd[topd-1]&&operd[topd];
                                topd--;
                            }
                            if(opert[topt]=='|')
                            {
                                operd[topd-1]=operd[topd-1]||operd[topd];
                                topd--;
                            }
                            topt--;
                        }
                        break;
                }
            }//else
        }//else
    }//while
        while(topt!=-1)
        {
            if(opert[topt]=='!')
            {
                operd[topd]=!operd[topd];
            }
            else if(opert[topt]=='&')
            {
                operd[topd-1]=operd[topd-1]&&operd[topd];
                topd--;
            }
            else if(opert[topt]=='|')
            {
                operd[topd-1]=operd[topd-1]||operd[topd];
                topd--;
            }
            topt--;
        }
        return operd[topd];
}









        

