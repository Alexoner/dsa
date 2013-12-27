/*
矩阵乘法C语言实现
Slyar 2009.3.20
*/
 
#include <stdio.h>
#include <stdlib.h>
 
/* 给 int 类型定义别名 datatype */
typedef int datatype;
 
/* 函数声明部分 */
datatype** Create(int m, int n);
void Reset(datatype**, int, int);
void Input(datatype**, int, int);
void Output(datatype**, int, int);
void MatrixMutiply(datatype**, datatype**, datatype**);
void MatrixFree(datatype** , int);
 
/* 定义三个矩阵的行列大小 */
int row_a, col_a;
int row_b, col_b;
int row_c, col_c;
 
/* 定义文件指针 */
FILE *fp;
 
int main()
{
        int i;
        datatype **a, **b, **c;
 
        /* 以只读方式打开输入文件 in.txt */
        if((fp = fopen("in.txt","r")) == NULL)
        {
                printf("Cannot open this file.\n");
                exit(0);
        }
 
        /* 创建并读入矩阵a */
        fscanf(fp,"%d%d", &row_a, &col_a);
        a=Create(row_a, col_a);
        Input(a,row_a, col_a);
 
        /* 创建并读入矩阵b */
        fscanf(fp,"%d%d", &row_b, &col_b);
        b = Create(row_b, col_b);
        Input(b,row_b, col_b);
 
        /* 关闭输入文件 */
        fclose(fp);
 
        /* 以写入方式打开输出文件 out.txt */
        if((fp = fopen("out.txt","w")) == NULL)
        {
                printf("Cannot open this file.\n");
                exit(0);
        }
 
        /* 判断两个矩阵能否相乘 */
        if(col_a == row_b)
        {
                row_c = row_a;
                col_c = col_b;
        }
        else
        {
                fprintf(fp,"Matrix Can't Mutiply !\n");
                exit(0);
        }
 
        /* 创建并初始化结果矩阵c */
        c = Create(row_c, col_c);
        Reset(c, row_c, col_c);
 
        /* 进行矩阵乘法运算 */
        MatrixMutiply(a, b, c);
 
        /* 输出结果矩阵C */
        Output(c, row_c, col_c);
 
        /* 关闭输出文件 */
        fclose(fp);
 
        /* 释放矩阵内存 */
        MatrixFree(a,row_a);
        MatrixFree(b,row_b);
        MatrixFree(c,row_c);
 
        //system("pause");
        return 0;
}
 
/* 为矩阵动态分配内存的函数 */
datatype** Create(int m, int n)
{
        int i;
        datatype **Matrix;
        Matrix = (datatype **) malloc(sizeof(datatype *) * m);
        for(i = 0; i < m; i++)
        {
                Matrix[i] = (datatype *) malloc(sizeof(datatype) * n);
        }
        return Matrix;
}
 
/* 初始化矩阵函数 */
void Reset(datatype** Matrix, int m, int n)
{
        int i,j;
        for(i = 0; i < m; i++)
        {
                for(j = 0; j < n; j++)
                {
                        Matrix[i][j] = 0;
                }
        }
}
 
/* 读入数据函数 */
void Input(datatype** Matrix, int m, int n)
{
        int i,j;
        for(i = 0; i < m; i++)
        {
                for(j = 0; j < n; j++)
                {
                        fscanf(fp,"%d", &Matrix[i][j]);
                }
        }
}
 
/* 输出数据函数 */
void Output(datatype** Matrix, int m, int n)
{
        int i,j;
        for(i = 0; i < m; i++)
        {
                for(j = 0; j < n; j++)
                {
                        fprintf(fp,"%d ", Matrix[i][j]);
                }
                fprintf(fp,"\n");
        }
}
 
/* 矩阵乘法运算函数 */
void MatrixMutiply(datatype** a, datatype** b, datatype** c)
{
        int i,j,k;
        for(i = 0; i < row_c; i++)
        {
                for(j = 0; j < col_c; j++)
                {
                        for(k = 0; k < col_a; k++)
                        {
                                c[i][j] += a[i][k] * b[k][j];
                        }
                }
        }
}
 
/* 释放矩阵内存函数 */
void MatrixFree(datatype** Matrix, int m)
{
        int i;
        for(i = 0; i < m; i++)
        {
                free(Matrix[i]);
        }
        free(Matrix);
}
