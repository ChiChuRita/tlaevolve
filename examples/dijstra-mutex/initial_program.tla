--------------------------- MODULE DijkstraMutex ---------------------------


EXTENDS Integers

CONSTANT Proc 


\* EVOLVE-BLOCK-START
(* --algorithm Mutex 
 { variables a = 0
   process (P \in Proc)
     skip;
 } *)
 \* EVOLVE-BLOCK-END


InCriticalSection(i) == pc[i] = "cs"
InNonCriticalSection(i) == pc[i] = "ncs"
TryingToEnterCriticalSection(i) == ~InCriticalSection(i) /\ ~InNonCriticalSection(i)

MutualExclusion == \A i, j \in Proc : 
                    (i # j) => ~ /\ InCriticalSection(i)
                                 /\ InCriticalSection(j)

LSpec == Init /\ [][Next]_vars 
          /\ \A self \in Proc: WF_vars((~InNonCriticalSection(self)) /\ P(self))

DeadlockFreedom == 
    \A i \in Proc : 
      TryingToEnterCriticalSection(i) ~> (\E j \in Proc : InCriticalSection(j))

=============================================================================
