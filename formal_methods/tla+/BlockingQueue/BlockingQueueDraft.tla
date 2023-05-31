--------------------------- MODULE BlockingQueueDraft ---------------------------

\*Learning resource from: https://github.com/lemmy/BlockingQueue

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       
--------------------------------------------------------------------------------------------------------
VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

--------------------------------------------------------------------------------------------------------
\*Bugfix: (logically) two mutexes
\*BUG[deadlock] Notify: producer notifies producer or consumer notifies consumer
Notify == IF waitSet # {}
        THEN \E t \in waitSet: waitSet' = waitSet \ {t}
        ELSE UNCHANGED waitSet

\* BUG: TLC deadlock. buffer <<p1>>, waitSet = {} immediately deadlock!?*)
\*NotifyOther(t) == 
\*    LET S == IF t \in Producers THEN waitSet \ Producers
\*            ELSE waitSet \ Consumers
\*    IN \E x \in S: waitSet' = waitSet \ {x}  

NotifyOther(t) == 
    LET S == IF t \in Producers THEN waitSet \ Producers
            ELSE waitSet \ Consumers
    IN IF S # {}
       THEN \E x \in S: waitSet' = waitSet \ {x}
       ELSE UNCHANGED waitSet  
    
--------------------------------------------------------------------------------------------------------
        
Wait(t) == /\ waitSet' = waitSet \cup {t}
          /\ UNCHANGED <<buffer>>         

-----------------------------------------------------------------------------

Put(t, d) ==
   \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(t)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)

Get(t) ==
   \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(t)
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSet = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)        
Next == \E t \in RunningThreads: \/ /\ t \in Producers
                                    /\ Put(t, t) \* Add some data to buffer
                                 \/ /\ t \in Consumers
                                    /\ Get(t)    

--------------------------------------------------------------------------------------------------------        
(* TLA+ is untyped, thus lets verify the range of some values in each state. *)

TypeOK == 
        /\ buffer \in Seq(Producers)
        /\ Len(buffer) \in 0..BufCapacity
        /\ waitSet \subseteq (Producers \cup Consumers)

--------------------------------------------------------------------------------------------------------

\*Invariants

(* No Deadlock *)        
NoDeadLock == waitSet # (Producers \cup Consumers)

Invariant == 
\*        TypeOK 
        /\ NoDeadLock

\*TODO: what's this?
THEOREM Init /\ [][Next]_vars => []NoDeadLock 

--------------------------------------------------------------------------------------------------------

\*TODO: ?
PutEnabled == \A p \in Producers : ENABLED Put(p, p)


\*https://learntla.com/core/temporal-logic.html
\*There are two kinds of temporal properties: 
\*    “safety” properties say our system doesn’t do bad things. 
\*    “liveness” properties say our system always does a good thing.
\*“We do not violate any database constraints” is safety, “All transactions either complete or roll back” is a liveness property. 
\*All invariants are safety properties, but not all safety properties are invariants.
\*temporal property of action expression

\*[] (always/"box")
\*[]P means that P is true in every state. When on the outside of a predicate, this is equivalent to an invariant, 
\*and in fact is how TLC supports them: writing INVARIANT P is the same as writing PROPERTY []P.
\*<>: eventually.
\*always eventually can be captured by state graph cycle where a xxx is enabled continously!


Spec == Init /\ [][Next]_vars


=============================================================================
\* Modification History
\* Last modified Wed Apr 05 17:47:05 CST 2023 by haodu
\* Created Wed Apr 05 14:49:41 CST 2023 by haodu
