---- MODULE Peterson ----
EXTENDS Naturals, TLC

\* Non-modifiable section (requirements)
ProcSet == {0, 1}

\* EVOLVE-BLOCK-START (PlusCal algorithm)
(* --algorithm PetersonAlgo
variables x = 0;

begin
  L0:
  while (TRUE) do
    \* EVOLVE-BLOCK-START
    L1:
      x := x; \* no-op stub
    \* EVOLVE-BLOCK-END
  end while;
end algorithm *)
\* EVOLVE-BLOCK-END

\* Invariant(s)
MutualExclusion == ~(pc[0] = "CS" /\ pc[1] = "CS")

====


