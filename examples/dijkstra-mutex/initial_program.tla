--------------------------- MODULE DijkstraMutex ---------------------------


EXTENDS Integers

CONSTANT Proc 


\* EVOLVE-BLOCK-START
(* --algorithm Mutex 
 { variables a = 0
   \* this is the initial sceleton program, replace this, including this comment
   process (P \in Proc)
     skip;
 } *)
 \* EVOLVE-BLOCK-END


InCriticalSection(i) == pc[i] = "CriticalSection"
InNonCriticalSection(i) == pc[i] = "NonCriticalSection"
TryingToEnterCriticalSection(i) == pc[i] = "TryingToEnter"

MutualExclusion == \A i, j \in Proc : 
                    (i # j) => ~ /\ InCriticalSection(i)
                                 /\ InCriticalSection(j)

LSpec == Init /\ [][Next]_vars 
          /\ \A self \in Proc: WF_vars((~InNonCriticalSection(self)) /\ P(self))

DeadlockFreedom == 
    \A i \in Proc : 
      TryingToEnterCriticalSection(i) ~> (\E j \in Proc : InCriticalSection(j))



=============================================================================
