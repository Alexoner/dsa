\* https://en.wikipedia.org/wiki/Readers%E2%80%93writer_lock#Using_two_mutexes
\* begin read: 3 steps, lock & increament, lock g, unlock r
\* The readers writer lock implemented with two mutexes: r, g.

-------------------- MODULE two_mutexes_rwlock --------------

EXTENDS Integers

CONSTANTS 
    Readers,
    Writers

VARIABLES
    r, \* mutex used by readers, protecting b
    g, \* global mutex, ensures mutual exclusion of writers
    pc, \* program counter
    b \* #blocking readers


vars == << r, g, pc, b>>
-------------------------------
Init == /\ b = 0
        /\ r = 0 \* unlocked
        /\ g = 0 \* unlocked
        /\ pc = [ x \in Readers \cup Writers |-> IF x \in Readers 
                        THEN "begin.read.lock_r"
                        ELSE "begin.write.lock_g" ]


-------------------------------
BeginReadLockR(t) == /\ pc[t] = "begin.read.lock_r"
                     /\ r = 0
                     /\ r' = t
                     /\ b' = b + 1
                     /\ pc' = [pc EXCEPT ![t] = "begin.read.lock_g"]
                     /\ UNCHANGED g

BeginReadLockG(t) == /\ pc[t] = "begin.read.lock_g"
                     /\ \/  /\ b = 1
                            /\ g = 0
                            /\ g' = t 
                            /\ pc' = [pc EXCEPT ![t] = "begin.read.unlock"]
                            /\ UNCHANGED << r, b >>
                        \/  /\ b # 1
                            /\ pc' = [pc EXCEPT ![t] = "begin.read.unlock"]
                            /\ UNCHANGED << r, g, b >>

BeginReadUnlock(t) == /\ pc[t] = "begin.read.unlock"
                       /\ r = t 
                       /\ r' = 0
                       /\ pc' = [pc EXCEPT ![t] = "end.read.lock_r"]
                       /\ UNCHANGED << g, b >>

------------------------------------------------------------------------------------------------

EndReadLockR(t) == /\ pc[t] = "end.read.lock_r"
                   /\ r = 0
                   /\ r' = t
                   /\ b' = b - 1
                   /\ pc' = [pc EXCEPT ![t] = "end.read.unlock"]
                   /\ UNCHANGED << g >>

\* multiple unlock can happen as an atomic event, unlike lock which must be separated into multiple steps
EndReadUnlock(t) == /\ pc[t] = "end.read.unlock"
                    /\  \/  /\ b = 0
                            /\ g # 0   \* thread acquired g may have already finished read, last reader or writer to finish to unlock
                            /\ g' = 0
                            /\ r' = 0
                            \* /\ pc = [pc EXCEPT ![t] = "finished"]
                        \/  /\ b # 0 
                            /\ r' = 0
                            /\ UNCHANGED <<g>>
                    /\ pc' = [pc EXCEPT ![t] = "begin.read.lock_r"]
                    /\ UNCHANGED b

------------------------------------------------------------------------------------------------

BeginWriteLockG(t) == /\ pc[t] = "begin.write.lock_g"
                      /\ g = 0
                      /\ g' = t
                      /\ pc' = [pc EXCEPT ![t] = "end.write.unlock"]
                      /\ UNCHANGED << r, b >>

EndWriteUnlock(t) ==    /\ pc[t] = "end.write.unlock"
                        /\ g' = 0
                        /\ pc' = [pc EXCEPT ![t] = "begin.write.lock_g"]
                        /\ UNCHANGED << b, r >> 

------------------------------------------------------------------------------------------------

Next == \/ \E t \in Readers:    \/ BeginReadLockR(t) 
                                \/ BeginReadLockG(t) 
                                \/ BeginReadUnlock(t)
                                \/ EndReadLockR(t)
                                \/ EndReadUnlock(t)
        \/ \E t \in Writers:    \/ BeginWriteLockG(t)
                                \/ EndWriteUnlock(t)

Spec == Init    
            /\ [][Next]_vars
            \* specify fairness to avoid meaningless infinite suttering
            /\ WF_vars(Next)  \* XXX: rule out indefinite crash: inifite stuttering after init
            /\ \A t \in Readers:    (/\ WF_vars(BeginReadUnlock(t))   \* unlock always eventually happens
                                    /\ WF_vars(EndReadUnlock(t)))
            /\ \A t1 \in Readers:  \* rule out reader starvation: all readers shall proceed
                /\ SF_vars(BeginReadLockR(t1))
                /\ SF_vars(BeginReadLockG(t1))
            \* /\ \A w \in Writers:    /\ WF_vars(EndWriteUnlock(w))
            \* /\ \E << t1, t2 >> \in Readers \X Writers: /\ WF_vars(BeginReadLockR(t1) \/ BeginWriteLockG(t2))

-------------------------
\* invariant
TypeOK == /\ b \in Nat
          /\ r \in Readers \cup Writers \cup {0}
          /\ g \in Readers \cup Writers \cup {0}
          /\ pc \in [ Readers \cup Writers -> {
            "begin.read.lock_r", "begin.read.lock_g", "begin.read.unlock",
            "end.read.lock_r", "end.read.unlock",
            "begin.write.lock_g", "end.write.unlock"
            } ]

\* ExclusiveWrite == (\E w \in Writers: pc[w] = "end.write.unlock") => 
\*                         /\ \A r \in Readers: pc[r] = "begin.read.lock_r"
\*                         /\ \A t \in Writers \ {w}: pc[w] = "begin.write.lock_g"
ExclusiveWrite == /\ \A <<w, t2>> \in Writers \X Readers: pc[w] = "end.write.unlock" => pc[t2] = "begin.read.lock_r"
                  /\ \A w1, w2 \in Writers: w1 # w2 /\ pc[w1] = "end.write.unlock" => pc[w2] = "begin.write.lock_g"

\* action properties

\* no deadlock

\* temporal properties
\* specify liveness: read, write must happen
\* no starvation. TODO: refine the property checking.
MultipleReaders == <>(b > 1) \* can support multiple readers read

NoReadStarvation == \A t \in Readers:   /\ []<>(<<BeginReadLockR(t)>>_vars)
                                        /\ []<>(<<BeginReadLockG(t)>>_vars)
NoWriteStarvation == \A w \in Writers: []<>(<<BeginWriteLockG(w)>>_vars)

NoStarvation == 
    /\ NoReadStarvation
    /\ NoWriteStarvation

===========================