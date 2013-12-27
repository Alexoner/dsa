#include <stdio.h>
#include <string.h>
#define MAX 65535

int bit[MAX],bit2[MAX];//use two arrays to store the bits of result of factory,upto 17471!

int main()
{
    int n,i,j,add,len,len2;//add: the number to be added to the higher bit,
    printf("please input the number n\n");
    while(scanf("%d",&n))
    {
        memset(bit,0,sizeof(bit));//initialize bit with 0
        memset(bit2,0,sizeof(bit2));//initialize bit2 with 0
        bit[0]=1;
        add=0;
        len=1;
        len2=0;
        for(i=1;i<=n;i++)
        {
            for(j=0;j<len;j++)//calculate bit by bit,and remember:use the REAL VALID LENGTH of the array!
            {
                bit[j]=bit[j]*i+add;
                add=bit[j]/1000000;
                bit[j]=bit[j]%1000000;
            }
            if(len==MAX)//overflow of the bit,then use bit2
            {
                for(j=0;j<len2;j++)
                {
                    bit2[j]=bit2[j]*i+add;
                    add=bit2[j]/1000000;
                    bit2[j]=bit2[j]%1000000;
                }
 
                while(add)
                {
                    len2++;
                    bit2[j++]=add%1000000;
                    add=add/1000000;
                }
           }
            else
                while(add)
                {
                    len++;
                    bit[j++]=add%1000000;
                    add=add/1000000;
                }
        }

         printf("the result is:\n");
        for(j=len2-1;j+1;j--)
            printf("%d",bit2[j]);
        for(j=len-1;j+1;j--)
            printf("%d",bit[j]);
        printf("\n");
    }
    return 0;
}


