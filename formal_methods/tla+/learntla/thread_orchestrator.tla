---- MODULE orchestrator ----
EXTENDS Integers, TLC, FiniteSets

Servers == {"s1", "s2"}

(*--algorithm threads
variables 
  online = Servers;

process orchestrator = "orchestrator"
begin
  Change:
    while TRUE do
      with s \in Servers do
       either
          await s \notin online;
          online := online \union {s};
        or
          await s \in online;
          await Cardinality(online) > 1;
          online := online \ {s};
        end either;
      end with;
    end while;
end process;


define
  Invariant == \E s \in Servers: s \in online
  Safety == \E s \in Servers: [](s \in online)  \* violated property
  \* It's not the case that all servers are always online
  Liveness == ~[](online = Servers)
end define;


end algorithm; *)
====


=============================================================================
\* Modification History
\* Last modified Tue Apr 04 10:36:49 CST 2023 by haodu
\* Created Tue Apr 04 10:01:57 CST 2023 by haodu
