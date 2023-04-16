\* Reference: https://github.com/Alexander-N/tla-specs/tree/main/dual-writes
\* Problem description: https://martin.kleppmann.com/2015/05/27/logs-for-data-infrastructure.html
\* Tips for complex modules:
\* - Always use TypeOK invariant
\* - Use print/Print for debugging, but remember print is called with bfs exhaustive!
\* - reduce states: symmetric sets, enforce order
\* - PlusCal for loop: goto, while.
\* - action profiling
\* DEBUG TLA+: https://emptysqua.re/blog/interactive-tla-plus/#visualizing-the-state-graph
\*
\* visualize:
\*  - either import Shiviz
\*  - or Set Host, Event, VectorClock variables.
\* run TLC, open MC.out, copy the state changes log
\* provide regular expression, requiring necessary named capture for event, host, clock.
\* upload log to https://bestchai.bitbucket.io/shiviz/   
\* TLA+ with ShiViz: https://github.com/tlaplus/tlaplus/issues/267

---------------------- MODULE dual_writes_vector_clock ----------------------


EXTENDS TLC, Integers, Sequences, SequencesExt, Functions, FiniteSets, Json \*, ShiViz
        , Naturals

CONSTANTS 
    Clients,
    Storage,      \* storage set,
    NULL

(* --algorithm dual_writes

variables

    \* Note: in actual systems, clients don't hold vector clock within servers scope, here for visualization
    vectorClock = [ x \in (Clients \cup Storage) |-> [ y \in (Clients \cup Storage) |-> 0 ] ];
    messages = [ x \in (Clients \cup Storage) |-> <<>> ];
    rxMsg = [ x \in (Clients \cup Storage) |-> NULL ];
    
    \* global variables for ShiViz 
    Host = NULL;
    Event = NULL;
    VectorClock = ToJsonObject([ x \in (Clients \cup Storage) |-> 0 ]);  \* needs to be json object
    
define

    targets == SetToSeq(Storage)  \* convert a set into a tuple

    max(a, b) == IF a >= b THEN a ELSE b
    \* vector clock operations
    Increment(clock, host) == [ clock EXCEPT ![host] = clock[host] + 1 ]
    MaxClock(clockA, clockB) == [ x \in DOMAIN clockA |-> max(clockA[x], clockB[x]) ]

end define

macro receive() begin
    await messages[self] # <<>>;

    rxMsg[self] := Head(messages[self]);
    messages[self] := Tail(messages[self]);

    vectorClock[self] := MaxClock(Increment(vectorClock[self], self), rxMsg[self].clock);
\*    print <<"receive", rxMsg[self].src, self, rxMsg[self].value>>;    
   
    Host := self;
    Event := pc[self];
    VectorClock := ToJsonObject(vectorClock[self]);

end macro;

macro send(dst, value) begin

    vectorClock[self] := Increment(vectorClock[self], self);

    messages[dst] := messages[dst] \o <<[
                src |-> self,
                dst |-> dst,
                clock |-> vectorClock[self],
                value |-> value
                ]>>;
\*    print <<"send", self, dst, value>>;    

    Host := self;
    Event := pc[self];
    VectorClock := ToJsonObject(vectorClock[self]);
end macro;

fair process client \in Clients
variables 
\*    writtenSet = {}; \* optimization: set to integer state, enforce order to remove permutation
    tx = 1; \* index for write
    rx = 1; \* index for read

begin
    Write:
\*        await tx =< Len(targets); \* put here as enabling condition, avoid 
        while tx =< Len(targets) do
\*            tx := CHOOSE x \in (Storage \ writtenSet): TRUE; \* inefficient: large state space
            send(targets[tx], self);
\*            print <<"write", self, targets[tx], targets, Storage >>;
            tx := tx + 1;
\*            writtenSet := writtenSet \cup {targets[tx]};

            \* disable the action in last step, to avoid a vanilla pc variable update after while break. 
            if tx > Len(targets)
            then
                goto ReceiveAck
            end if;

        end while;

    ReceiveAck:
            receive();
            rx := rx + 1;
            if rx =< Len(targets)
            then 
                goto ReceiveAck;
            end if;
        
end process;

fair process storage \in Storage
variables
    value = NULL;
    i = 0;

begin
    ReceiveMsg:
        await messages[self] # <<>> /\ rxMsg[self] = NULL;
\*        while messages[self] # <<>> /\ rxMsg[self] = NULL do
            receive();
            value := rxMsg[self].value;
\*        end while;

\*    LoseMsg:
\*        ;
    SendACK:
        await rxMsg[self] # NULL;
        send(rxMsg[self].src, NULL);
        rxMsg[self] := NULL;
        
        i := i + 1;
        
        if i < 2
        then
            goto ReceiveMsg;  \* Note: Pluscal, need goto, or while to avoid termination.
        end if;
        
end process;


end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "7b8f5cb7" /\ chksum(tla) = "808a3ac")
VARIABLES vectorClock, messages, rxMsg, Host, Event, VectorClock, pc

(* define statement *)
targets == SetToSeq(Storage)

max(a, b) == IF a >= b THEN a ELSE b

Increment(clock, host) == [ clock EXCEPT ![host] = clock[host] + 1 ]
MaxClock(clockA, clockB) == [ x \in DOMAIN clockA |-> max(clockA[x], clockB[x]) ]

VARIABLES tx, rx, value, i

vars == << vectorClock, messages, rxMsg, Host, Event, VectorClock, pc, tx, rx, 
           value, i >>

ProcSet == (Clients) \cup (Storage)

Init == (* Global variables *)
        /\ vectorClock = [ x \in (Clients \cup Storage) |-> [ y \in (Clients \cup Storage) |-> 0 ] ]
        /\ messages = [ x \in (Clients \cup Storage) |-> <<>> ]
        /\ rxMsg = [ x \in (Clients \cup Storage) |-> NULL ]
        /\ Host = NULL
        /\ Event = NULL
        /\ VectorClock = ToJsonObject([ x \in (Clients \cup Storage) |-> 0 ])
        (* Process client *)
        /\ tx = [self \in Clients |-> 1]
        /\ rx = [self \in Clients |-> 1]
        (* Process storage *)
        /\ value = [self \in Storage |-> NULL]
        /\ i = [self \in Storage |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Write"
                                        [] self \in Storage -> "ReceiveMsg"]

Write(self) == /\ pc[self] = "Write"
               /\ IF tx[self] =< Len(targets)
                     THEN /\ vectorClock' = [vectorClock EXCEPT ![self] = Increment(vectorClock[self], self)]
                          /\ messages' = [messages EXCEPT ![(targets[tx[self]])] =      messages[(targets[tx[self]])] \o <<[
                                                                                   src |-> self,
                                                                                   dst |-> (targets[tx[self]]),
                                                                                   clock |-> vectorClock'[self],
                                                                                   value |-> self
                                                                                   ]>>]
                          /\ Host' = self
                          /\ Event' = pc[self]
                          /\ VectorClock' = ToJsonObject(vectorClock'[self])
                          /\ tx' = [tx EXCEPT ![self] = tx[self] + 1]
                          /\ IF tx'[self] > Len(targets)
                                THEN /\ pc' = [pc EXCEPT ![self] = "ReceiveAck"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Write"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "ReceiveAck"]
                          /\ UNCHANGED << vectorClock, messages, Host, Event, 
                                          VectorClock, tx >>
               /\ UNCHANGED << rxMsg, rx, value, i >>

ReceiveAck(self) == /\ pc[self] = "ReceiveAck"
                    /\ messages[self] # <<>>
                    /\ rxMsg' = [rxMsg EXCEPT ![self] = Head(messages[self])]
                    /\ messages' = [messages EXCEPT ![self] = Tail(messages[self])]
                    /\ vectorClock' = [vectorClock EXCEPT ![self] = MaxClock(Increment(vectorClock[self], self), rxMsg'[self].clock)]
                    /\ Host' = self
                    /\ Event' = pc[self]
                    /\ VectorClock' = ToJsonObject(vectorClock'[self])
                    /\ rx' = [rx EXCEPT ![self] = rx[self] + 1]
                    /\ IF rx'[self] =< Len(targets)
                          THEN /\ pc' = [pc EXCEPT ![self] = "ReceiveAck"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << tx, value, i >>

client(self) == Write(self) \/ ReceiveAck(self)

ReceiveMsg(self) == /\ pc[self] = "ReceiveMsg"
                    /\ messages[self] # <<>> /\ rxMsg[self] = NULL
                    /\ messages[self] # <<>>
                    /\ rxMsg' = [rxMsg EXCEPT ![self] = Head(messages[self])]
                    /\ messages' = [messages EXCEPT ![self] = Tail(messages[self])]
                    /\ vectorClock' = [vectorClock EXCEPT ![self] = MaxClock(Increment(vectorClock[self], self), rxMsg'[self].clock)]
                    /\ Host' = self
                    /\ Event' = pc[self]
                    /\ VectorClock' = ToJsonObject(vectorClock'[self])
                    /\ value' = [value EXCEPT ![self] = rxMsg'[self].value]
                    /\ pc' = [pc EXCEPT ![self] = "SendACK"]
                    /\ UNCHANGED << tx, rx, i >>

SendACK(self) == /\ pc[self] = "SendACK"
                 /\ rxMsg[self] # NULL
                 /\ vectorClock' = [vectorClock EXCEPT ![self] = Increment(vectorClock[self], self)]
                 /\ messages' = [messages EXCEPT ![(rxMsg[self].src)] =      messages[(rxMsg[self].src)] \o <<[
                                                                        src |-> self,
                                                                        dst |-> (rxMsg[self].src),
                                                                        clock |-> vectorClock'[self],
                                                                        value |-> NULL
                                                                        ]>>]
                 /\ Host' = self
                 /\ Event' = pc[self]
                 /\ VectorClock' = ToJsonObject(vectorClock'[self])
                 /\ rxMsg' = [rxMsg EXCEPT ![self] = NULL]
                 /\ i' = [i EXCEPT ![self] = i[self] + 1]
                 /\ IF i'[self] < 2
                       THEN /\ pc' = [pc EXCEPT ![self] = "ReceiveMsg"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << tx, rx, value >>

storage(self) == ReceiveMsg(self) \/ SendACK(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: client(self))
           \/ (\E self \in Storage: storage(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))
        /\ \A self \in Storage : WF_vars(storage(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

---------------------

TypeOK ==   /\ vectorClock \in [ (Clients \cup Storage) -> [ (Clients \cup Storage) -> Nat ] ]
                /\ rxMsg \in [ (Clients \cup Storage) -> [
                                    src: Clients \cup Storage,
                                    dst: Clients \cup Storage,
                                    clock: [ Clients \cup Storage -> Nat ],
                                    value: Clients \cup Storage \cup {NULL}
                                ] \cup {NULL}
                             ]
--------------------------

ClockMonotonicallyIncrease == TRUE

OnlyIncreases ==    /\ \A c \in Clients: <>[][rx'[c] > rx[c]]_rx
                    /\ \A c \in Clients: <>[][tx'[c] > tx[c]]_tx
                    /\ \A s \in Storage: <>[][i'[s] > i[s]]_i
                    /\ \A x, y \in Clients \cup Storage: <>[][vectorClock'[x][y] > vectorClock[x][y]]_vectorClock

\* temporal action property: liveness propperty    
AllValuesEqual ==
    \A s1, s2 \in Storage: value[s1] = value[s2]
EventuallyConsistent == <>[]AllValuesEqual

=============================================================================
\* Modification History
\* Last modified Sat Apr 15 17:01:45 CST 2023 by haodu
\* Created Wed Apr 12 16:29:33 CST 2023 by haodu
