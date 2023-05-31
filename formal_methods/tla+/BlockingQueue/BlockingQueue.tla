--------------------------- MODULE BlockingQueue ---------------------------

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
Notify == IF waitSet # {}
        THEN \E t \in waitSet: waitSet' = waitSet \ {t}
        ELSE UNCHANGED waitSet
\*BUG[deadlock] Notify: producer notifies producer or consumer notifies consumer
\*Bugfix: (logically) two mutexes
NotifyOther(t) == 
    LET S == IF t \in Producers THEN waitSet \ Producers
            ELSE waitSet \ Consumers
    IN \E x \in S: waitSet' = waitSet \ {x}


\*NotifyOtherFair(t) == 
\*    LET S == IF t \in Producers THEN waitSet \ Producers ELSE waitSet \ Consumers
\*    IN     
    
--------------------------------------------------------------------------------------------------------
        
Wait(t) == /\ waitSet' = waitSet \cup {t}
          /\ UNCHANGED <<buffer>>         

Put(t, d) == 
    \/  /\ Len(buffer) = BufCapacity
        /\ Wait(t)
    \/  /\ Len(buffer) < BufCapacity
        /\ buffer' = Append(buffer, d)
\*        /\ Notify
        /\ NotifyOther(t) 
    
     
Get(t) == 
    \/  /\ buffer = <<>>
        /\ Wait(t)
    \/  /\ Len(buffer) > 0
        /\ buffer' = Tail(buffer)
\*        /\ Notify
        /\ NotifyOther(t)

--------------------------------------------------------------------------------------------------------
(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSet = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)        
Next == \E t \in RunningThreads:
    \/  /\ t \in Producers
        /\ Put(t, t) 
    \/   t \in Consumers         
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

\*Individual Producer or Consumer threads can starve because we haven't specified fair,
\*except for weak fairness of Next to avoid the trivial counter-example of stuttering after Init
FairSpec == Spec 
            /\ WF_vars(Next) \* weak fairness for Next, rules out forever crashes
            /\ \A p \in Producers : WF_vars(Put(p, p)) \* can even specify (weak) fairness at the level of the ```Put``` sub-actions 


\*rules out starvation completely?
AdvancedFairSpec == 
    /\ Spec

    \* Assert that producers take steps should their  Put  action be (continuously) 
    \* enabled. This is the basic case of fairness that rules out stuttering, i.e.,
    \* assert global progress.
    /\ \A t \in Producers:
            WF_vars(Put(t,t)) 
    \* Stipulates that  Get  actions (consumers!) will eventually notify *all*
    \* waiting producers. In other words, given repeated  Get  actions (we don't
    \* care which consumer, thus, existential quantification), all waiting
    \* producers will eventually be notified.  Because  Get  actions are not
    \* continuously enabled (the buffer might be empty), weak fairness is not
    \* strong enough. Obviously, no real system scheduler implements such an
    \* inefficient "policy".
    \* This fairness constraint was initially proposed by Leslie Lamport, although
    \* with the minor typo "in" instead of "notin", which happens to hold for
    \* configurations with at most two producers.
    /\ \A t \in Producers:
            SF_vars(\E self \in Consumers: Get(self) /\ t \notin waitSet')

    \* See notes above (except swap "producer" with "consumer").
    /\ \A t \in Consumers:
            WF_vars(Get(t)) 
    /\ \A t \in Consumers:
            SF_vars(\E self \in Producers: Put(self, self) /\ t \notin waitSet')

--------------------------------------------------------------------------------------------------------

(* All producers will continuously be serviced. For this to be violated,    *)
(* ASSUME Cardinality(Producers) > 1 has to hold (a single producer cannot  *)
(* starve itself).                                                          *)
\*Reference: introduced by https://github.com/lemmy/BlockingQueue/commit/fc0f62267d6d35bb7d1cdf857110a5fc219e0b34
NoStarvation == \A p \in Producers: []<>(<<Put(p, p)>>_vars)


--------------------------------------------------------------------------------------------------------
                
=============================================================================
\* Modification History
\* Last modified Wed Apr 05 11:37:44 CST 2023 by haodu
\* Created Sat Apr 01 15:50:43 CST 2023 by haodu
