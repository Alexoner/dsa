#ifndef DSADEF_H
#define DSADEF_H

#undef offsetof
#define offsetof(TYPE, MEMBER) ((size_t) &((TYPE *)0)->MEMBER)

//"asm" and "typeof" are keywords in gnu* modes,the variants
//__asm__ and __typeof__ are recognized in all modes
#define container_of(ptr, type, member) ({                      \
        const __typeof__( ((type *)0)->member ) *__mptr = (ptr);    \
        (type *)( (char *)__mptr - offsetof(type,member) );})

#define prefetch

#endif
