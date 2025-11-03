---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC, Sequences


Missionaries == {"M1", "M2", "M3"}
Cannibals    == {"C1", "C2", "C3"}
People       == Missionaries \cup Cannibals

\* EVOLVE-BLOCK-START
(* --algorithm MissionariesAndCannibals {
variables
  left = People,
  right = {},
  boat = "left";

\* Implement a single crossing here, which can then be called multiple times in the main method
procedure CrossRiver(Passgs) {
  skip:
}

\* Main Method
{
\* Call the CrossRiver method here in the correct order to solve the problem
}

} *)
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
ProperBoatMove ==
  [] [Next => (UNCHANGED <<left, right, boat>> \/ ProperMove)]_vars

\* Goal / Liveness
AllAcross == right = People
ReachGoal == <>AllAcross


==== 