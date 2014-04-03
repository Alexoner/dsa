#include <stdio.h>

/**
 * From: http://gcc.gnu.org
 *
 * It is often useful to merge two tokens into one while expanding macros.
 * This is called token pasting or token concatenation. The ‘##’ preprocessing
 * operator performs token pasting. When a macro is expanded, the two tokens on
 * either side of each ‘##’ operator are combined into a single token, which then
 * replaces the ‘##’ and the two original tokens in the macro expansion. Usually
 * both will be identifiers, or one will be an identifier and the other a
 * preprocessing number. When pasted, they make a longer identifier.
 * This isn't the only valid case. It is also possible to concatenate
 * two numbers (or a number and a name, such as 1.5 and e3) into a number.
 * Also, multi-character operators such as += can be formed by token pasting.
 */
