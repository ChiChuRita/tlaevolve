---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC


Missionaries == {"M1", "M2", "M3"}
Cannibals    == {"C1", "C2", "C3"}
People       == Missionaries \cup Cannibals

\* EVOLVE-BLOCK-START
(* --algorithm Algorithm {
variables
  left = People,
  right = {},
  boat = "left";

\* Helper Method for a single Crossing
procedure CorssRiver(Passgers) {
  skip:
}

\* Main Method
{
S1:  call Move({"C1", "C2"}); \* Example Call
}

} *)
\* EVOLVE-BLOCK-END


\* Dont touch anything below this line, this is for the TLC model checker
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