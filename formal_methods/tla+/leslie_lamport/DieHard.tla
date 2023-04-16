------------------------------ MODULE DieHard ------------------------------

EXTENDS Integers

VARIABLES big, small

typeOk == /\ small \in 0..3
          /\ big \in 0..5
          
Init == /\ small = 0
        /\ big = 0

FillSmall == /\ small' = 3
              /\ big' = big

EmptySmall == /\ small' = 0
              /\ big' = big
                       
              
FillBig == /\ big' = 5
           /\ small' = small
                   
EmptyBig == /\ big' = 0
            /\ small' = small

Small2Big == /\ IF big + small =< 5
                THEN /\ big' = big + small
                     /\ small' = 0
                ELSE /\ big' = 5
                     /\ small' = small - (5 - big)
                     
Big2Small == /\ IF big + small < 3    
               THEN /\ big' = 0 
                    /\ small' = big + small
               ELSE /\ small' = 3
                     /\ big' = big - (3 - small)
Next == \/ FillSmall
        \/ EmptySmall
        \/ FillBig
        \/ EmptyBig
        \/ Small2Big
        \/ Big2Small
        
\*IN
          

=============================================================================
\* Modification History
\* Last modified Mon Mar 27 11:33:57 CST 2023 by haodu
\* Created Mon Mar 27 10:37:58 CST 2023 by haodu
