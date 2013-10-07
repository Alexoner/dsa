
#include <stdio.h>
int mdays(int y,int m)
{

       if (m==2) return (y%4==0 && (y%100==0 || y%400==0))?29:28;
       else if (m==4 || m==6 || m==9 || m==11) return 30;
       else return 31;
}

main()
{
       int y,m,d,days;
       printf("Enter year:");
       scanf("%d",&y);
       printf("Enter month:");
       scanf("%d",&m);
       printf("Enter day:");
       scanf("%d",&d);
       days=d;
       while(m>1){days+=mdays(y,m-1);m--;}
       printf("%d\n",days);
}
