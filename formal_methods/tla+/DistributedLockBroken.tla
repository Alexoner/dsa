\*https://medium.com/@polyglot_factotum/modelling-distributed-locking-in-tla-8a75dc441c5a

----------------------- MODULE DistributedLockBroken -----------------------

(*
{}, \in: set operators
[]: sequences, function, 
<<>>: tuple 
-> function mapping from domain to range

Models the read-modify-write cycle.
*)

EXTENDS Integers, Sequences

CONSTANTS NULL, 
        NumThreads

VARIABLES
    lock,           (* lock service: lock holder*)
    lastWrittenBy,  (* shared storage service: write *)
    threads         (* client threads as writter of the storage *)
    
vars == << lock, lastWrittenBy, threads >>     
       

LOCK_STATUS == {"acquired", "released"}
Threads == 1..NumThreads
    
Init == /\ lock = NULL
        /\ lastWrittenBy = NULL
        /\ threads = [ x \in Threads |-> [ id |-> x, step |-> "released" ] ]
        
TypeOK ==   /\ lock \in Threads \cup {NULL}
            /\ lastWrittenBy \in Threads \cup {NULL}
            /\ threads \in [ 1..NumThreads -> [ id : 1..NumThreads, step: LOCK_STATUS ] ]

Acquire(t) ==   /\ lock = NULL
                /\ lock' = t
                /\ threads' = [ threads EXCEPT ![t].step = "acquired"]
                /\ UNCHANGED <<lastWrittenBy>>
                
Release(t) ==   /\ lock = t
                /\ lock' = NULL
                /\ lastWrittenBy' = NULL
                /\ threads ' = [threads EXCEPT ![t].step = "released"]   
                  
Write(t, d) ==  /\ threads[t].step = "acquired"
                /\                          \* BUG: missed this bullet boolean operator
                    \/  /\ lock = t  \* difference with IF THEN ELSE?
                        /\ lastWrittenBy' = t
                        /\ UNCHANGED <<lock, threads>>
                    \/  /\ lock # t  \* FIX(lock expired): fencing token, shared resources check lock
                        /\ UNCHANGED <<lock, lastWrittenBy, threads>>

\* client doesn't know it's been paused and the lock has expired
Expire(t) == /\ threads[t].step = "acquired"
             /\ lock = t
             /\ lock' = NULL
             /\ lastWrittenBy' = NULL
             /\ UNCHANGED <<threads>>                                   
            
Next ==  /\ \E t \in Threads:   \/ Acquire(t)
                                \/ Write(t, t)
                                \/ Release(t)
                                \/ Expire(t)
Spec == Init /\ [][Next]_vars

\* safety invariants
\* each write should be from a client holding the lock
Protected == lastWrittenBy # NULL => lastWrittenBy = lock
\* only one client acquired the lock. But in reality all clients can think they hold the lock
\*Exclusive ==    LET S == SelectSeq(threads, LAMBDA x: x.step = "acquired")
\*                IN Len(S) =< 1

\* can't be achieved if the client holding lock got suspended indefinitely
\*Consistent == lock # NULL => threads[lock].step = "acquired"                


=============================================================================
\* Modification History
\* Last modified Sat Apr 08 17:13:31 CST 2023 by haodu
\* Created Wed Apr 05 20:04:10 CST 2023 by haodu
