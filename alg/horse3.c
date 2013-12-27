#include<stdio.h>
#define N 5
struct nx
{
   int m;
   int n;   
};
int array[9][9];
int count;
void format(void)
{
   int line;
   int posi;
   for(line=1;line<=8;line++)
   {
      for(posi=1;posi<=8;posi++)
      {
         array[line][posi]=0;
      }
   }
}

struct nx jump_horse(int direct,int x,int y)
{
   struct nx next;
   switch(direct)
   {
      case 1: next.m=x+2;next.n=y+1;break;
      case 2: next.m=x+2;next.n=y-1;break;
      case 3: next.m=x+1;next.n=y-2;break;
      case 4: next.m=x-1;next.n=y-2;break;
      case 5: next.m=x-2;next.n=y-1;break;
      case 6: next.m=x-2;next.n=y+1;break;
      case 7: next.m=x-1;next.n=y+2;break;
      case 0: next.m=x+1;next.n=y+2;break;
   }
   return next;
}

int can_put_here(int deepth,int m,int n)
{
   if(n>N||m>N||n<1||m<1||array[m][n]!=0)
     return 0;
   else
      return 1;
}

void list_result(void)
{
   int line;
   int posi;
   for(line=1;line<=N;line++)
   {
      for(posi=1;posi<=N;posi++)
      {
         printf("%3d",array[line][posi]);
      }
       printf("\n");
   }
   printf("\n");
}

void horse_track(int deepth,int x,int y)
{
   int direct1;
   struct nx next;
   if(deepth>N*N)
   {
      list_result();
      array[x][y]=0;
      count++;/*看有多少種走法*/
   }
   else
   {
      for(direct1=0;direct1<=7;direct1++)
      {
        next=jump_horse(direct1,x,y);
        if(can_put_here(deepth,next.m,next.n))
        {
           array[next.m][next.n]=deepth;
           horse_track(deepth+1,next.m,next.n);
        }
     }
     if(direct1==8)
       array[x][y]=0;
   }
}

main()
{
   int startx;
   int starty;
   format();
   printf("Please input the start position(x,y):");
   scanf("%d%d",&startx,&starty);
   array[startx][starty]=1;
   count=0;
   horse_track(2,startx,starty);
   printf("%d",count);
} 
