--------------------------- MODULE DijkstraMutex ---------------------------
EXTENDS Naturals, TLC

\* Non-modifiable section (requirements)
ProcIds == {0, 1}

\* EVOLVE-BLOCK-START (PlusCal algorithm)
(* --algorithm PetersonAlgo
variables
  x = 0,
  intent = [i \in ProcIds |-> FALSE],
  turnOwner = 0;

process Proc \in ProcIds
begin
Loop:
  while TRUE do
Entry:
    intent[self] := TRUE;
    turnOwner := 1 - self;
    await ~intent[1 - self] \/ turnOwner = self;
CS:
    x := x;
Exit:
    intent[self] := FALSE;
  end while;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "e0aa0565" /\ chksum(tla) = "52c3ebe3")
VARIABLES x, intent, turnOwner, pc

vars == << x, intent, turnOwner, pc >>

ProcSet == (ProcIds)

Init == (* Global variables *)
        /\ x = 0
        /\ intent = [i \in ProcIds |-> FALSE]
        /\ turnOwner = 0
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ pc' = [pc EXCEPT ![self] = "Entry"]
              /\ UNCHANGED << x, intent, turnOwner >>

Entry(self) == /\ pc[self] = "Entry"
               /\ intent' = [intent EXCEPT ![self] = TRUE]
               /\ turnOwner' = 1 - self
               /\ ~intent'[1 - self] \/ turnOwner' = self
               /\ pc' = [pc EXCEPT ![self] = "CS"]
               /\ x' = x

CS(self) == /\ pc[self] = "CS"
            /\ x' = x
            /\ pc' = [pc EXCEPT ![self] = "Exit"]
            /\ UNCHANGED << intent, turnOwner >>

Exit(self) == /\ pc[self] = "Exit"
              /\ intent' = [intent EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "Loop"]
              /\ UNCHANGED << x, turnOwner >>

Proc(self) == Loop(self) \/ Entry(self) \/ CS(self) \/ Exit(self)

Next == (\E self \in ProcIds: Proc(self))

Spec == Init /\ [][Next]_vars

MutualExclusion == ~(pc[0] = "CS" /\ pc[1] = "CS")

\* END TRANSLATION 
\* EVOLVE-BLOCK-END
\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Wed Oct 29 17:30:27 PDT 2025 by emilscheffer
\* Last modified Sat Jan 01 12:14:14 PST 2011 by lamport
\* Created Fri Dec 31 14:14:14 PST 2010 by lamport
