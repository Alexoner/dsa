---- MODULE hourclock ----
EXTENDS Naturals
\* TODO: two clocks
(*--algorithm hourclock
variable hr = 1; \* hour

begin
  A:
    while TRUE do
        if hr = 12 then
          hr := 1;
        else
            hr := hr + 1;
        end if;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2cb5c6e4" /\ chksum(tla) = "f749b589")
VARIABLE hr

vars == << hr >>

Init == (* Global variables *)
        /\ hr = 1

Next == IF hr = 12
           THEN /\ hr' = 1
           ELSE /\ hr' = hr + 1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====


=============================================================================
\* Modification History
\* Last modified Wed Apr 05 09:26:45 CST 2023 by haodu
\* Created Wed Apr 05 09:25:50 CST 2023 by haodu
