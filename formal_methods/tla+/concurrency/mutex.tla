\* mutex specification with PlusCal C-syntax

(*
struct futex_mutex
{
    void lock()
    {
        if (state.exchange(locked, std::memory_order_acquire) == unlocked)
            return;
        while (state.exchange(sleeper, std::memory_order_acquire) != unlocked)
        {
            syscall(SYS_futex, &state, FUTEX_WAIT_PRIVATE, sleeper, nullptr, nullptr, 0);
        }
    }
    void unlock()
    {
        if (state.exchange(unlocked, std::memory_order_release) == sleeper)
            syscall(SYS_futex, &state, FUTEX_WAKE_PRIVATE, 1, nullptr, nullptr, 0);
    }
 
private:
    std::atomic<unsigned> state{unlocked};
 
    static constexpr unsigned unlocked = 0;
    static constexpr unsigned locked = 1;
    static constexpr unsigned sleeper = 2;
};

*)

------------ MODULE mutex -----------

EXTENDS  Integers, Sequences

CONSTANT 
    Threads

(*
--algorithm futex_mutex {

variables futex_state = 0, futex_sleepers = {};

macro compare_and_swap(source, value) {
    old_value := source;
    source := value;
}

\* futex

procedure futex_wait(val = 0) {
check_state:
    if (futex_state # val){
        return;
    } else {
        futex_sleepers := futex_sleepers \union {self};
wait_for_wake:
        await self \notin futex_sleepers;  \* XXX: has to be put in another label for next action, contradicting above statement!
        return;
    };
}

procedure futex_wake_single() {
check_sleepers:
    if (futex_sleepers # {})
    {
        with (x \in futex_sleepers) {
            futex_sleepers := futex_sleepers \ {x};
        };
    };

    return;
}

procedure futex_wake_all() {
futex_wake_all:
    futex_sleepers := {};
    return; \* XXX: miss this, pc set to "Error"
}

\* mutex

procedure mutex_lock()
variables old_value = 0; \* local variables are restored by return statement.
{
lock_exchange:
    compare_and_swap(futex_state, 1);
check:
    if (old_value = 0) {
        return;
    };
sleep_loop:
    compare_and_swap(futex_state, 2);
sleep_check:
    if (old_value = 0) return;
    else call futex_wait(2);
    goto sleep_loop;
}

procedure mutex_unlock() 
variables old_value = 0; \* local variables are restored by return statement.
{
unlock_exchange:
    compare_and_swap(futex_state, 0);
check_if_sleeper:
    if (old_value = 2) {
        call futex_wake_single();
        return; \* XXX: explicit return matching call operator
    }
    else return;
}

fair process (worker \in Threads) {
start:- \* -: exempt from fairness declaration
    while (TRUE) {
        call mutex_lock();
    cs: skip;
        call mutex_unlock();
    }
}

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "96ff0738" /\ chksum(tla) = "5b0ac82")
\* Label futex_wake_all of procedure futex_wake_all at line 76 col 5 changed to futex_wake_all_
\* Procedure variable old_value of procedure mutex_lock at line 83 col 11 changed to old_value_
VARIABLES futex_state, futex_sleepers, pc, stack, val, old_value_, old_value

vars == << futex_state, futex_sleepers, pc, stack, val, old_value_, old_value
        >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ futex_state = 0
        /\ futex_sleepers = {}
        (* Procedure futex_wait *)
        /\ val = [ self \in ProcSet |-> 0]
        (* Procedure mutex_lock *)
        /\ old_value_ = [ self \in ProcSet |-> 0]
        (* Procedure mutex_unlock *)
        /\ old_value = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

check_state(self) == /\ pc[self] = "check_state"
                     /\ IF futex_state # val[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED futex_sleepers
                           ELSE /\ futex_sleepers' = (futex_sleepers \union {self})
                                /\ pc' = [pc EXCEPT ![self] = "wait_for_wake"]
                                /\ UNCHANGED << stack, val >>
                     /\ UNCHANGED << futex_state, old_value_, old_value >>

wait_for_wake(self) == /\ pc[self] = "wait_for_wake"
                       /\ self \notin futex_sleepers
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << futex_state, futex_sleepers, old_value_, 
                                       old_value >>

futex_wait(self) == check_state(self) \/ wait_for_wake(self)

check_sleepers(self) == /\ pc[self] = "check_sleepers"
                        /\ IF futex_sleepers # {}
                              THEN /\ \E x \in futex_sleepers:
                                        futex_sleepers' = futex_sleepers \ {x}
                              ELSE /\ TRUE
                                   /\ UNCHANGED futex_sleepers
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << futex_state, val, old_value_, 
                                        old_value >>

futex_wake_single(self) == check_sleepers(self)

futex_wake_all_(self) == /\ pc[self] = "futex_wake_all_"
                         /\ futex_sleepers' = {}
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << futex_state, val, old_value_, 
                                         old_value >>

futex_wake_all(self) == futex_wake_all_(self)

lock_exchange(self) == /\ pc[self] = "lock_exchange"
                       /\ old_value_' = [old_value_ EXCEPT ![self] = futex_state]
                       /\ futex_state' = 1
                       /\ pc' = [pc EXCEPT ![self] = "check"]
                       /\ UNCHANGED << futex_sleepers, stack, val, old_value >>

check(self) == /\ pc[self] = "check"
               /\ IF old_value_[self] = 0
                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ old_value_' = [old_value_ EXCEPT ![self] = Head(stack[self]).old_value_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "sleep_loop"]
                          /\ UNCHANGED << stack, old_value_ >>
               /\ UNCHANGED << futex_state, futex_sleepers, val, old_value >>

sleep_loop(self) == /\ pc[self] = "sleep_loop"
                    /\ old_value_' = [old_value_ EXCEPT ![self] = futex_state]
                    /\ futex_state' = 2
                    /\ pc' = [pc EXCEPT ![self] = "sleep_check"]
                    /\ UNCHANGED << futex_sleepers, stack, val, old_value >>

sleep_check(self) == /\ pc[self] = "sleep_check"
                     /\ IF old_value_[self] = 0
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ old_value_' = [old_value_ EXCEPT ![self] = Head(stack[self]).old_value_]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ val' = val
                           ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                            pc        |->  "sleep_loop",
                                                                            val       |->  val[self] ] >>
                                                                        \o stack[self]]
                                   /\ val' = [val EXCEPT ![self] = 2]
                                /\ pc' = [pc EXCEPT ![self] = "check_state"]
                                /\ UNCHANGED old_value_
                     /\ UNCHANGED << futex_state, futex_sleepers, old_value >>

mutex_lock(self) == lock_exchange(self) \/ check(self) \/ sleep_loop(self)
                       \/ sleep_check(self)

unlock_exchange(self) == /\ pc[self] = "unlock_exchange"
                         /\ old_value' = [old_value EXCEPT ![self] = futex_state]
                         /\ futex_state' = 0
                         /\ pc' = [pc EXCEPT ![self] = "check_if_sleeper"]
                         /\ UNCHANGED << futex_sleepers, stack, val, 
                                         old_value_ >>

check_if_sleeper(self) == /\ pc[self] = "check_if_sleeper"
                          /\ IF old_value[self] = 2
                                THEN /\ /\ old_value' = [old_value EXCEPT ![self] = Head(stack[self]).old_value]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                                 pc        |->  Head(stack[self]).pc ] >>
                                                                             \o Tail(stack[self])]
                                     /\ pc' = [pc EXCEPT ![self] = "check_sleepers"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ old_value' = [old_value EXCEPT ![self] = Head(stack[self]).old_value]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << futex_state, futex_sleepers, val, 
                                          old_value_ >>

mutex_unlock(self) == unlock_exchange(self) \/ check_if_sleeper(self)

start(self) == /\ pc[self] = "start"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_lock",
                                                        pc        |->  "cs",
                                                        old_value_ |->  old_value_[self] ] >>
                                                    \o stack[self]]
               /\ old_value_' = [old_value_ EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "lock_exchange"]
               /\ UNCHANGED << futex_state, futex_sleepers, val, old_value >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_unlock",
                                                     pc        |->  "start",
                                                     old_value |->  old_value[self] ] >>
                                                 \o stack[self]]
            /\ old_value' = [old_value EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "unlock_exchange"]
            /\ UNCHANGED << futex_state, futex_sleepers, val, old_value_ >>

worker(self) == start(self) \/ cs(self)

Next == (\E self \in ProcSet:  \/ futex_wait(self)
                               \/ futex_wake_single(self)
                               \/ futex_wake_all(self) \/ mutex_lock(self)
                               \/ mutex_unlock(self))
           \/ (\E self \in Threads: worker(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : /\ WF_vars((pc[self] # "start") /\ worker(self))
                                 /\ WF_vars(mutex_lock(self))
                                 /\ WF_vars(mutex_unlock(self))
                                 /\ WF_vars(futex_wait(self))
                                 /\ WF_vars(futex_wake_single(self))

\* END TRANSLATION 

----------------------------------------------------


MutualExclusion == \A i, j \in ProcSet:
    i # j => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Trying(i) == pc[i] \in { "exchange_lock", "check", "sleep_loop", "sleep_check", "check_state", "wait_for_wake" }

DeadlockFree == \A i \in ProcSet:
    Trying(i) ~> \E j \in ProcSet: pc[j] = "cs" \* enters critical section


================================

