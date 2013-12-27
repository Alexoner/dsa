/*            骑士巡游问题
*      Author: meng_luckywolf   
*           Date:2008-3-26
*/

//打印出所有可能路径

#include <stdio.h>
#include <stdlib.h>


#define SIZE_OF_BOARD 5
#define TRUE 1
#define FALSE 0

//跳跃的八个方向
//(a[i],b[i])对应一种跳法
int a[8]={2,1,-1,-2,-2,-1,1,2};//the arrays  declare the direction of ecah jump
int b[8]={1,2,2,1,-1,-2,-2,-1};
int sum;


int h[SIZE_OF_BOARD*SIZE_OF_BOARD]={0}; //二维数组，存储路径

char success;
char success1;

void PrintResult(int h[])
{
 int i,j;
 for (i=0;i<SIZE_OF_BOARD;i++) 
 {
  for (j=0;j<SIZE_OF_BOARD;j++) 
  {
   printf("%2d ",h[i*SIZE_OF_BOARD+j]);
  }
  printf("\n");
 }

 printf("\n\n");
}

//i:第i次跳跃；x,y:当前横纵坐标；
void Try(int i,int x,int y)
{
 int next;
 int xNext,yNext; //下一步的横纵坐标

// printf("begin the %d step\n",i);
 for (next=0;next<8;next++) 
 {
  xNext = x + a[next];
  yNext = y + b[next];

  if ( xNext>=0 && xNext<SIZE_OF_BOARD && yNext>=0 && yNext<SIZE_OF_BOARD ) 
  {
   if ( h[xNext*SIZE_OF_BOARD+yNext] == 0 ) 
   {
    //0表示x,y未经过，故将其赋i
    h[xNext*SIZE_OF_BOARD+yNext] = i;

    if (i < SIZE_OF_BOARD*SIZE_OF_BOARD) 
    {
     Try(i+1,xNext,yNext);
    }
    else 
    {
        sum++;
     PrintResult(h);
//     getchar();
    }
    h[xNext*SIZE_OF_BOARD+yNext] = 0;
   }
  
  }
 }
}


void main()
{
 int x,y;

 x = 0;
 y = 0;//从(x,y)起跳
 h[x*SIZE_OF_BOARD+y] = 1;
 Try(2,x,y);
 printf("there are %d kinds of method\n",sum);
}
