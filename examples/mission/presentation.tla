---- MODULE System ----

(*
High-Level Summary
- This system models bears and deers crossing a river using a boat, with a safety constraint that deers must not be outnumbered by bears on either bank.
- Objective: move all animals to the far bank without ever violating the safety constraint.
- Assumptions: none beyond what is stated; all open points are listed below as questions.
- Out of scope: swimming, additional species, external interventions other than moving the boat.
*)

\* EVOLVE-BLOCK-START
EXTENDS Naturals, FiniteSets, TLC, Sequences

CONSTANTS
  NBears0,
  NDeers0,
  Capacity

(*--algorithm Algorithm {
    \* Here goes the algorithm
}*)

\* EVOLVE-BLOCK-END


\* Derived / helper operators
bearsRight == NBears0 - bearsLeft
deersRight == NDeers0 - deersLeft

SafeBank(b, d) == (d = 0) \/ (b <= d)

TypeOK ==
  /\ bearsLeft \in 0..NBears0
  /\ deersLeft \in 0..NDeers0
  /\ boatOnLeft \in BOOLEAN

\* Invariants
\* Trace: merged bullets: "bears do not outnumber deers" + "safety applies only when deers > 0"
Inv_Safety ==
  /\ SafeBank(bearsLeft, deersLeft)
  /\ SafeBank(bearsRight, deersRight)

\* Trace: totals constant + each animal has exactly one location
Inv_TotalsConstant ==
  /\ bearsLeft + bearsRight = NBears0
  /\ deersLeft + deersRight = NDeers0

\* Sanity: initial values match declared initialization
Inv_InitState ==
  Init =>
    /\ bearsLeft = NBears0
    /\ deersLeft = NDeers0
    /\ boatOnLeft = TRUE

\* Properties
AllOnRight == /\ bearsLeft = 0 /\ deersLeft = 0

\* Goal: eventually all animals are on the far bank
Prop_Goal == <> AllOnRight

\* Expected crossing action
Act_Cross ==
  /\ boatOnLeft' = ~boatOnLeft
  /\ \E xb_ \in 0..NBears0, xd_ \in 0..NDeers0 :
        /\ xb_ + xd_ \in 1..Capacity
        /\ IF boatOnLeft
              THEN /\ xb_ \leq bearsLeft
                   /\ xd_ \leq deersLeft
                   /\ bearsLeft' = bearsLeft - xb_
                   /\ deersLeft' = deersLeft - xd_
              ELSE /\ xb_ \leq bearsRight
                   /\ xd_ \leq deersRight
                   /\ bearsLeft' = bearsLeft + xb_
                   /\ deersLeft' = deersLeft + xd_

\* Constrain Next to be a crossing step (allow stuttering at termination)
ConstrainNext ==
  [] [Next => (UNCHANGED <<bearsLeft, deersLeft, boatOnLeft>> \/ Act_Cross)]_vars

\* Fairness: weak fairness for the main step relation
FairSpec == Spec /\ WF_vars(Next)


====
