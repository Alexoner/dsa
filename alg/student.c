#include <stdio.h>
#include <string.h>
#define MAX 64
typedef struct student
{
    //char *id;//use pointer or array big enough to store string
    //char *name;
    char id[MAX];
    char name[MAX];
    int score;
}Student;

int search(Student *s,int n,char *id)
{
    int j,k,l;
    for(j=0;j<n;j++)
    {
        l=strlen(s[j].id);
        for(k=0;k<l&&s[j].id[k]==id[k];k++);
                if(k==l)
                return j;
    }
    printf("no match\n");
    return -1;
}


int main()
{
    char id[MAX];
    int i,j;
    Student stu[4]=
    {
        {"1004","TOM",100},//char array needs ""
        {"1002","LILY",95},
        {"1001","ANN",93},
        {"1003","LUCY",98}
    };//array 
    for(i=0;i<4;i++)
    {
        printf("id: %s\n",stu[i].id);
    }
    printf("please input the id\n");
    scanf("%s",id);
    printf("id is%s\n",id);
    i=search(stu,4,id);
    if(i==-1)
        return 0;
    printf("id:%s\n",stu[i].id);
    printf("\nname:%s\n",stu[i].name);
    printf("score:%d\n",stu[i].score);
    return 0;
}

