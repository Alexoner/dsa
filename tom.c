#include <stdio.h>
int main()
{
    int i,j,k;
    printf("There are many different methods\n");
    for(i=1;i<6;i++)
        for(j=1;j<6;j++)
            for(k=1;k<6;k++)
                if(i!=j&&i!=k&&j!=k)
                    printf("(%d,%d,%d)",i,j,k);
    printf("\n");
    return 0;
}
