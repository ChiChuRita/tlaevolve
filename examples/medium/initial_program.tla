--------------------------- MODULE LRUCache ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Keys, Values, Capacity, Requests, NoKey

ElemSet(s) == { s[i] : i \in 1..Len(s) }

IsUnique(seq) == \A i, j \in 1..Len(seq): i # j => seq[i] # seq[j]

\* EVOLVE-BLOCK-START
(* --algorithm LRUAlgo
 {
   variables present = {},
             values = [k \in Keys |-> CHOOSE v \in Values: TRUE],
             order = << >>,
             i = 0,
             lastAccess = [k \in Keys |-> 0],
             evicted = NoKey;

   \* Initial skeleton to be evolved by OpenEvolve
   skip;
 } *)
\* EVOLVE-BLOCK-END

\* Invariants (safety properties)
TypeOK ==
  /\ present \subseteq Keys
  /\ values \in [Keys -> Values]
  /\ order \in Seq(Keys)
  /\ i \in 0..Len(Requests)
  /\ lastAccess \in [Keys -> 0..Len(Requests)]
  /\ evicted \in (Keys \cup {NoKey})

CapacityBound == Len(order) <= Capacity

OrderMatchesPresent ==
  /\ IsUnique(order)
  /\ ToSet(order) = present

====


