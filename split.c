#include <stdio.h>
#include <stdlib.h>
int L=0;
void print(int res[], int num) 
{
    L++;
    printf("%8d:",L);
    for (int i = 0; i < num; ++i) {
        printf("%d ", res[i]);
    }
    printf("\n");
}
void split(int n, int m) 
{// n表示总数，m表示最大因子
    static int res[100];// 保存结果
    static int num = -1;// 当前因子下标
    num++;

    if (0 == n) 
    {// 递归终止条件，为0不可再分，直接输出
        print(res, num+1);
        num--;
        return;
    }
    else 
    {
        if (n == m) 
        {// 不拆，直接输出
            res[num] = m;
            print(res,num+1);
            num--;
        } 
        else 
        {
            // 拆分出第一个
            res[num] = m;
            n = n-m;

            if (m>n) m = n; // 最大因子不可能大于总数

            for (int i = m; i>=1; --i) 
            {// 循环，第二个因子可以继续拆分，而且按照最大因子不同可以拆分成多个
                split(n, i);
            }
            num--;
        }
    }
}
void Split(int n) 
{
    if (n<=0) return;
    if (1==n) 
    {
        L++;
        printf("%8d:1 \n",L);
        return;
    }
    if (100<n) 
    {
        printf("Up to 100\n");
        return;
    }
    for (int i = n-1; i>=1; i--) 
    {
        split(n, i);
    }
}
void main(int argc,char **argv) 
{
    if (argc<=1) Split(5);
    else Split(atoi(argv[1]));
}
