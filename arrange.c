#include <stdio.h>
#define MAX 10

int used[MAX];
int arrange[MAX];
int n;


void put(int m)
{
    if(m>=n+1)
    {
        printf("%d \n",arrange[n]);
        return ;
    }
    else
    {
        int i,j,use;//used stores the number that has been used
        for(i=1;i<=n;i++)
        {
            use=0;
            for(j=1;j<m;j++)
                if(i==used[j])
                {
                   use=1;
                   break;
                }
            if(use)
            {
                //printf("%d has been used in used[%d],for another\n",i,j);
                continue;
            }
            used[m]=i;
            arrange[m]=arrange[m-1]*10+i;
            put(m+1);
            //put(++m);
            //m--;//This is the CRITICAL STATEMENT!otherwise,backtrack is wrong!!
        }
    }
}

int main()
{
    arrange[0]=0;
    used[0]=0;
    printf("please input the number from 1-9!\n");
    scanf("%d",&n);
    printf("now producing the arrangement!\n");
    put(1);
    printf("completed successfully!\n");
    return 0;
}

