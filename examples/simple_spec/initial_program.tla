---- MODULE Simple ----
EXTENDS Naturals, TLC

\* Non-modifiable section (requirements)

\* EVOLVE-BLOCK-START (PlusCal algorithm)
(* --algorithm SimpleAlgo
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
SafeBounds == x \in {0, 1}

====


