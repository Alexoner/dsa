## TAIL RECURSION
Tail recursion, constructs solution at the end of the recursion by passing intermediate 
solution along down recursive calls as function arguments
Non tail recursion procedure, we need to restore variable state or construct the solution
at the top level call.

## Methods to transform a recursion algorithm to iterative one
 All iterative algorithms can be described recursively. So recursive algorithms can be reformed 
 into iterative ones, vise versa. 

### GENERAL STEPS
 
1. Convert FUNCTION ARGUMENTS and RETURN ADDRESSES into variable STATES.
2. Manually implement STACK on heap memory to simulate the recursive call process. Store those
variable STATES in STACKS.

## BOTTOM-UP: like LEXICOGRAPHICAL ORDER
For routines that don't involve backtracking, the algorithm will be straightforward so that there
is no need to maintain explicit stacks. Some single variables will just do because we don't need to backtrack
and the actual stack depth won't be less than a constant.

## Optimization to recursion algorithms rather than just translating

### DYNAMIC PROGRAMMING
- Optimal substructure
- Overlapping subproblems
- STATE TRANSITION
- BACKTRACK to generate the solution
