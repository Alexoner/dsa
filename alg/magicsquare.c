#include <stdio.h>
#include <stdlib.h>
#define MAX_SIZE 15
int main()
{
    static int square[MAX_SIZE][MAX_SIZE];//the number in each square
    int i,j,row,column,size;//index of the 2 dimension array
    int count;//the numbers to be filled in
    printf("please input the size :\n");
    if(scanf("%d",&size))//length of square
        printf("now processing\n");
    else
        exit(1);
    if(size<1||size>MAX_SIZE)//out of range
    {
        printf("out of range\n");
        exit(1);
    }

    for(i=0;i<size;i++)
        for(j=0;j<size;j++)
            square[i][j]=0;
    i=0;
    j=(size-1)/2;
    square[i][j]=1;
    for(count=2;count<size*size+1;count++)
    {
        row=(i-1<0)?size-1:i-1;//up
        column=(j-1<0)?size-1:j-1;//left
        if(square[row][column])//there is already a number
            i=(i+1)%3;//select the downside one
        else//select 
        {
            i=row;
            j=column;
        }
        square[i][j]=count;
    }
    
    printf("the magicsquare:\n");
    for(i=0;i<size;i++)//print the square
    {
        for(j=0;j<size;j++)
            printf("%5d",square[i][j]);
        printf("\n");
    }
    return 0;
}





