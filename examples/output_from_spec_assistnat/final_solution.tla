------------------------------ MODULE Untitled ------------------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences
(*--algorithm Algorithm {
variables
  \* Problem data (inline constants for this script)
  Missionaries = {"M1", "M2", "M3"},
  Cannibals    = {"C1", "C2", "C3"},
  People       = Missionaries \cup Cannibals,

  \* State
  left = People,
  right = {},
  boat = "left";

procedure Move(P) {
Cross:
  if (boat = "left") {
    left  := left \ P;
    right := right \cup P;
    boat  := "right";
  } else {
    right := right \ P;
    left  := left \cup P;
    boat  := "left";
  };
  return;
}

{
  \* Fixed solution sequence
  S1:  call Move({"C1", "C2"});
  S2:  call Move({"C1"});
  S3:  call Move({"C1", "C3"});
  S4:  call Move({"C2"});
  S5:  call Move({"M1", "M2"});
  S6:  call Move({"M1", "C1"});
  S7:  call Move({"M1", "M3"});
  S8:  call Move({"C3"});
  S9:  call Move({"C1", "C2"});
  S10: call Move({"C1"});
  S11: call Move({"C1", "C3"});
  Finish:
    skip;
}
}*)


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

\* Intentionally false invariants (state predicates) to be checked as INVARIANTS
\* Fails early: once the first crossing sends the boat to the right
Inv_FailsEarly ==
  boat = "left"

\* Fails later: once three people are on the right bank
Inv_FailsLater ==
  Cardinality(right) < 3
====