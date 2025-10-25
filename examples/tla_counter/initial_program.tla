---- MODULE Counter ----
EXTENDS Naturals, TLC

\* Non-modifiable section (requirements)
CONSTANTS Max, MaxDepth
VARIABLES x, step
vars == <<x, step>>

Init == /\ x = 0
        /\ step = 0

Bounded == step < MaxDepth

WithinBounds == x \in 0..Max

\* EVOLVE-BLOCK-START
\* You may redefine Next and any helper actions it uses. Keep variables and constants unchanged.

Inc == /\ Bounded
       /\ x < Max
       /\ x' = x + 1
       /\ step' = step + 1

Dec == /\ Bounded
       /\ x > 0
       /\ x' = x - 1
       /\ step' = step + 1

Stutter == /\ ~Bounded /\ UNCHANGED vars

Next == Inc \/ Dec \/ Stutter
\* EVOLVE-BLOCK-END

Spec == Init /\ [][Next]_vars

====


