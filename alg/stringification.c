#include <stdio.h>

/**
 * Sometimes you may want to convert a macro argument into a string constant.
 * Parameters are not replaced inside string constants, but you can use the ‘#’
 * preprocessing operator instead. When a macro parameter is used with a leading ‘#’,
 * the preprocessor replaces it with the literal text of the actual argument,
 * converted to a string constant. Unlike normal parameter replacement,
 * the argument is not macro-expanded first. This is called stringification.
 */

#define WARN_IF(EXP) \
    do { if (EXP) \
    fprintf(stderr,"Warning: " #EXP "\n");}\
while(0)

int main()
{
    int x = 0;
    WARN_IF (x == 0);

}

