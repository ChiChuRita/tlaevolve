---- MODULE HardQueue ----
\* EVOLVE-BLOCK-START
EXTENDS Naturals, Sequences, TLC

CONSTANTS ProducerIds, ConsumerIds, Capacity, MaxSeq

Items == [pid: ProducerIds, seq: 0..(MaxSeq - 1)]

ElemSet(s) == { s[i] : i \in 1..Len(s) }

IsUnique(seq) == \A i, j \in 1..Len(seq): i # j => seq[i] # seq[j]

(* --algorithm HardQueueAlgo {
  variables stubVar = 0;

  process (Dummy = 0)
  {
  DummyLoop:
    while (TRUE) {
      skip;
    };
  };
} *)

\* Invariants (safety properties)
TypeOK ==
  /\ buf \in Seq(Items)
  /\ produced \in Seq(Items)
  /\ consumed \in Seq(Items)
  /\ nextSeq \in [ProducerIds -> 0..MaxSeq]

BufferBounded == Len(buf) <= Capacity

ProducedUnique == IsUnique(produced)

ConsumedUnique == IsUnique(consumed)

NoSpuriousConsumption == ElemSet(consumed) \subseteq ElemSet(produced)

PerProducerFIFO ==
  \A p \in ProducerIds:
    \A i, j \in 1..Len(consumed):
      i < j /\ consumed[i].pid = p /\ consumed[j].pid = p => consumed[i].seq < consumed[j].seq

\* Liveness / progress properties
AllProduced == \A p \in ProducerIds: nextSeq[p] = MaxSeq

EventuallyAllProduced == <> AllProduced

EventuallyDrained == <> (Len(buf) = 0 /\ ElemSet(consumed) = ElemSet(produced))

\* Disallow steps that only stutter on the main state variables
NoStutter == ~UNCHANGED <<buf, produced, consumed, nextSeq>>

====


