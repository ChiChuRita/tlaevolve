---- MODULE Simple ----
EXTENDS Naturals, TLC

\* EVOLVE-BLOCK-START
(* --algorithm SimpleAlgo
variables c, x = 0;
begin
  Loop:
  while (x < 10) do
    x := x + 1;
  end while;
end algorithm *)
\* EVOLVE-BLOCK-END

\* Invariant(s)
SafeBounds == x \in {0, 1, 2, 3}

====


