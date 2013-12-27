#include <stdio.h>
int main()
{
    int m,n,ok,c;
    c=0,ok=0;
    printf("please input two numbers\n");
    if(!scanf("%d",&m))
            return 0;
    if(!scanf("%d",&n))
        return 0;
    while(m%10||n%10)
    {
        c=c+m%10+n%10;
        if(c>9)
        {
            c=1;
            ok++;
        }
        else 
            c=0;
         m=m/10;
         n=n/10;
    }
    printf("there are %dtimes\n",ok);
    return 0;
}



