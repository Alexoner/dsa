\* https://leetcode.com/problems/n-queens/
\* this module finds only one solution
\* TODO: how to find all solutions without exhausting the state space?
\* TODO: how to count states satisfying a certain condition?
\*      => maintain such states explicitly as variables?
\* solve this with dfs, places queens row by row

\* Note: TLA+ is exhaustive BFS seach by default, we just need to specify state transition
\* Answer: solve this without backtracking! Use bfs!
 
\* reference: https://github.com/kaelzhang81/Examples/blob/master/specifications/N-Queens/Queens.tla 

------------------------ MODULE NQueensAllSolutions ------------------------

EXTENDS Integers, Sequences

CONSTANTS N

VARIABLES
    queue,  \* search frontier
    ans
    
vars == <<queue, ans>>    

Init == /\ queue = { <<>> }
        /\ ans = {}
        
\* functions
Abs(x) == IF x < 0 THEN -x ELSE x    
CanAttack(rows, i, j, v) ==     \/ rows[i] = v
                                \/ Abs(rows[i] - v) = Abs(i - j)     \* slope is 1, -1

--------------------------

\* FIXME: not finding solution yet
PlaceBUG == \E board \in queue: 
    LET j == (Len(board) + 1)
        
    IN    \* BUG: off by one error, Len(board)
            /\ \E v \in 1..N:   \* can place queue at jth row at column v
                /\ \A i \in 1..(j-1): ~CanAttack(board, i, j, v)
                /\  \/  /\ j = N    \* found an answer
                        /\ ans' = ans \cup {board}
                        /\ queue' = queue \ {board}
                    \/  /\ j < N
                        /\ UNCHANGED <<ans>>
                        /\ LET board1 == board \o <<v>> IN 
                            queue' = queue \cup {board1}
\*                            queue' = (queue \ {board}) \cup {board1}  \* pop out from queue

Place == \E board \in queue:
    LET j == (Len(board) + 1)
        cols == { v \in 1..N : (\A i \in 1..(j-1): ~CanAttack(board, i, j, v)) } \* bfs: edge
        neighbours == { board \o <<v>>: v \in cols }  \* bfs: next vertices
    IN
    /\  \/  /\ j = N
\*            /\ cols # {}   \* BUG: can't be put here, forming disjunct enabling condition j=N /\ cols # {}
            /\ queue' = (queue \ {board})            
            /\ ans' = ans \cup neighbours
        \/  /\ j < N
            /\ queue' = (queue \ {board}) \cup neighbours
            /\ UNCHANGED ans

Next ==     \/ Place

Spec == Init /\ [][Next]_vars

NotTerminated ==    /\ queue # {}
\*                    /\ ans = {}


=============================================================================
\* Modification History
\* Last modified Sat Apr 08 20:31:00 CST 2023 by haodu
\* Created Sat Apr 08 18:23:18 CST 2023 by haodu
