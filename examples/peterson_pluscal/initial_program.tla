---- MODULE Peterson ----
EXTENDS Naturals, TLC

\* Non-modifiable section (requirements)
ProcSet == {0, 1}

\* EVOLVE-BLOCK-START
(* --algorithm PetersonAlgo
variables
  flag = [i \in ProcSet |-> FALSE],
  turn = 0;

process (p \in ProcSet)
variables other = 1 - self;
begin
  Loop:
  while (TRUE) do
    NonCS:
      skip;
    Entry:
      flag[self] := TRUE;
      turn := other;
    Wait:
      while (flag[other] /\ turn = other) do
        skip;
      end while;
    CS:
      skip;
    Exit:
      flag[self] := FALSE;
  end while;
end process
end algorithm *)
\* EVOLVE-BLOCK-END

\* Invariant(s)
MutualExclusion == ~(pc[0] = "CS" /\ pc[1] = "CS")

====


