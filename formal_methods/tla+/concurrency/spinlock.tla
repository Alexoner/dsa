\* spinlock specification with Pluscal C-syntax(instead of P-syntax).
\* simulating function calls with stack.

(*

struct bad_spinlock
{
    void lock()
    {
        while (locked.exchange(true))
        {
        }
    }
    void unlock()
    {
        locked.store(false);
    }
  
private:
    std::atomic<bool> locked{false};
};

*)

------------------------- MODULE spinlock -------------------------

EXTENDS Integers, Sequences

CONSTANT Threads 

(*
--algorithm Spinlock 
{
variables locked = FALSE;

procedure lock() 
variables old_value = TRUE;
{
exchange: 
    old_value := locked;
    locked := TRUE;
check:
    if (old_value) {
        goto exchange;
    }  else {
        return;
    }
}

procedure unlock() {
reset_state:
    locked := FALSE;
    return;
}

fair process (P \in Threads) {
loop:-
    while (TRUE) {
        call lock();  \* call procedure 
    cs:
        skip;
        call unlock();
    }
}

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "cef2b3f2" /\ chksum(tla) = "35c6a7dc")
VARIABLES locked, pc, stack, old_value

vars == << locked, pc, stack, old_value >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ locked = FALSE
        (* Procedure lock *)
        /\ old_value = [ self \in ProcSet |-> TRUE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "loop"]

exchange(self) == /\ pc[self] = "exchange"
                  /\ old_value' = [old_value EXCEPT ![self] = locked]
                  /\ locked' = TRUE
                  /\ pc' = [pc EXCEPT ![self] = "check"]
                  /\ stack' = stack

check(self) == /\ pc[self] = "check"
               /\ IF old_value[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "exchange"]
                          /\ UNCHANGED << stack, old_value >>
                     ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ old_value' = [old_value EXCEPT ![self] = Head(stack[self]).old_value]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED locked

lock(self) == exchange(self) \/ check(self)

reset_state(self) == /\ pc[self] = "reset_state"
                     /\ locked' = FALSE
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED old_value

unlock(self) == reset_state(self)

loop(self) == /\ pc[self] = "loop"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                       pc        |->  "cs",
                                                       old_value |->  old_value[self] ] >>
                                                   \o stack[self]]
              /\ old_value' = [old_value EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "exchange"]
              /\ UNCHANGED locked

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                     pc        |->  "loop" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "reset_state"]
            /\ UNCHANGED << locked, old_value >>

P(self) == loop(self) \/ cs(self)

Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
           \/ (\E self \in Threads: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : /\ WF_vars((pc[self] # "loop") /\ P(self))
                                 /\ WF_vars(lock(self))
                                 /\ WF_vars(unlock(self))

\* END TRANSLATION 

MutualExclusion == \A i, j \in ProcSet: 
    i # j => ~ (pc[i] = "cs" /\ pc[j] = "cs")

DeadlockFreedom == \A i \in ProcSet:
    pc[i] = "exchange" ~> \E j \in ProcSet: pc[j] = "cs"


======================================================================
