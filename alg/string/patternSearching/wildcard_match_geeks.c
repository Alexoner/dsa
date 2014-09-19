/*http://www.geeksforgeeks.org/wildcard-character-matching*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct ABC
{
    char c;
    int id;
};
int main()
{
    int n, m, i = 0, top = 0, set = 0, j = 0, setB = 0, star = 0, i_back,
              j_back;
    char s1[100], s2[100];
    scanf("%s", s1);

    scanf("%s", s2);
    n = strlen(s1);
    m = strlen(s2);
    struct ABC *A = (struct ABC *)malloc(sizeof(struct ABC) * n);

    while (s1[i] != '*' && s1[i] && s2[j])
    {

        if (s1[i] != s2[j] && s1[i] != '?')
        {
            printf("NO");
            return 0;
        }
        else
        {
            i++;
            j++;
        }
    }
    i_back = n - 1;
    j_back = m - 1;
    while (s1[i_back] != '*' && i_back >= 0 && j_back >= 0)
    {
        if (s1[i_back] != s2[j_back] && s1[i_back] != '?')
        {
            printf("NO");
            return 0;
        }
        else
        {
            i_back--;
            j_back--;
        }
    }

    for (; i < i_back + 1; i++)
    {
        if (s1[i] == '*')
        {
            star = 1;
            /*A[top].c='?';
            A[top++].id=set;
            */
            set = 0;
        }

        if (s1[i] != '*')
        {
            A[top].c = s1[i];
            A[top++].id = set++;
        }
    }

    /*for(i=0;i<top;i++)
            printf("%c",A[i].c);*/

    i = 0;
    set = 0;
    n = strlen(s2);
    while (i < top && j < j_back + 1)
    {

        if (A[i].c == s2[j] || A[i].c == '?')
        {
            if (A[i].id == 0)
            {
                set = i;
                i++;
                j++;
                setB = j;
            }
            else
            {
                if (A[i - 1].c == s2[j - 1] || A[i - 1].c == '?')
                {
                    i++;
                    j++;
                }
                else
                {
                    j = setB;
                    i = set;
                }
            }
        }

        else
            j++;
    }

    if (i == top && star == 1)
        printf("YeS");
    else if (i == top && star == 0)
    {
        if (strlen(s1) == strlen(s2))
            printf("YES");
        else
            printf("NO");
    }
    else
        printf("No");

    return 0;
}
