#include <stdio.h>
#include <stdlib.h>
#define MAX 128
int main()
{
	int a[5],i;
	int base[4]={25,10,5,1},s;
	printf("please input a number n=");
	if(!scanf("%d",a))
	{
		printf("error input\n");
		exit(0);
	}
	for(i=0;i<4;i++)
	{
		if(!a[i])
			break;
		a[i+1]=a[i]%base[i];
		s=(a[i]-a[i+1])/base[i];
		printf("%d of  base[%d]=%d\n",s,i,base[i]);
	}
	while(getchar()!=EOF);
	return 0;
}



