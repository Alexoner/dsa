\* https://redis.io/commands/incr/#pattern-rate-limiter-2
\* https://github.com/Alexander-N/tla-specs/tree/main/rate-limiter
\* model the race condition where set expire is not called at all
\* model the system as a sequence of discrete events!!
\* race condition: redis doesn't support read modify write cycle without lua script.
\* solution: 
\*  - lua script
\*  - counter[IP][time bucket]
(*
FUNCTION LIMIT_API_CALL(ip):
current = GET(ip)
IF current != NULL AND current > 10 THEN
    ERROR "too many requests per second"
ELSE
    value = INCR(ip)
    IF value == 1 THEN
        EXPIRE(ip,1)
    END
    PERFORM_API_CALL()
END
*)

---------------------------- MODULE RateLimiter ----------------------------
EXTENDS Integers

CONSTANTS 
    Limit,
    NumThreads

VARIABLES 
    counter,
    shouldExpire,  \* expiration is a timestamp, but abstracted as action enabling boolean  
    pc
    
vars == << counter, shouldExpire, pc >>

Threads == 1..NumThreads

typeOK ==   /\ counter \in Nat
            /\ pc \in { "get", "incr", "setExpire" }

-------------------------------------------------------------------------------

Init == /\ counter = 0
        /\ pc = [t \in Threads |-> "get"]
        /\ shouldExpire = FALSE

Get(t) ==   /\ pc[t] = "get"
            /\ counter < Limit
            /\ pc' = [pc EXCEPT ![t] = "incr"]
            /\ UNCHANGED <<counter, shouldExpire>>

Incr(t) ==  /\ pc[t] = "incr"
            /\ pc' = [pc EXCEPT ![t] = "setExpire"]
            /\ counter' = counter + 1
            /\ UNCHANGED << shouldExpire>>        

SetExpire(t) == /\ pc[t] = "setExpire"
                /\  \/  /\ counter = 1
                        /\ UNCHANGED <<counter>>
                        /\ shouldExpire' = TRUE
                        /\ pc' = [ pc EXCEPT ![t] = "get" ]
                    \/  /\ counter # 1
                        /\ UNCHANGED <<counter, shouldExpire>>
                        /\ pc' = [ pc EXCEPT ![t] = "get" ]
\*                    \/  /\ pc' = "ERROR"
\*                        /\ UNCHANGED << counter, shouldExpire >>

-------------------------------------------------------------------------------

Expire ==   /\ shouldExpire = TRUE
            /\ counter' = 0
            /\ shouldExpire' = FALSE
            /\ UNCHANGED pc

-------------------------------------------------------------------------------        

Next == \/ \E t \in Threads:
            \/ Get(t)
            \/ Incr(t)
            \/ SetExpire(t)
        \/ Expire
    
Spec == Init /\ [][Next]_vars    



=============================================================================
\* Modification History
\* Last modified Sat Apr 08 15:03:41 CST 2023 by haodu
\* Created Sat Apr 08 11:42:42 CST 2023 by haodu
