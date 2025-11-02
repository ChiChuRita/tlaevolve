---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC


\* EVOLVE-BLOCK-START
(* --algorithm SimpleAlgo
Assumes elsewhere (from your PlusCal translation or TLA+ spec):
- CONSTANTS People, Missionaries, Cannibals
- VARIABLES left, right, boat
- Init, Next, Spec          (e.g., Spec == Init /\ [][Next]_vars)
- vars == << left, right, boat >>
end algorithm *)
\* EVOLVE-BLOCK-END

\* Basic helpers
CountM(S) == Cardinality(S \cap Missionaries)
CountC(S) == Cardinality(S \cap Cannibals)
SafeBank(S) == (CountM(S) = 0) \/ (CountM(S) >= CountC(S))

FairSpec == Spec /\ WF_vars(Next)

\* Invariants
TypeOK ==
  /\ left \subseteq People /\ right \subseteq People
  /\ left \cap right = {}
  /\ left \cup right = People
  /\ boat \in {"left","right"}

Safe ==
  /\ SafeBank(left)
  /\ SafeBank(right)

AllStartLeft ==
  /\ left = People
  /\ right = {}
  /\ boat = "left"

InitialConditionOK == Init => AllStartLeft

Passengers ==
  IF boat = "left" THEN left \ left' ELSE right \ right'

ProperMove ==
  /\ boat' # boat
  /\ Cardinality(Passengers) \in {1, 2}
  /\ IF boat = "left" THEN
        /\ left'  = left \ Passengers
        /\ right' = right \cup Passengers
     ELSE
        /\ right' = right \ Passengers
        /\ left'  = left \cup Passengers

\* Every real Next-step must look like a proper move; stuttering is allowed.
ProperBoatMove == []( [Next]_vars => UNCHANGED vars \/ ProperMove )

\* Goal / Liveness
AllAcross == right = People
ReachGoal == <>AllAcross


==== 