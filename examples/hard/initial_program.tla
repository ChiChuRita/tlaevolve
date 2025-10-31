---- MODULE HardQueue ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS ProducerIds, ConsumerIds, Capacity, MaxSeq

Items == [pid: ProducerIds, seq: 0..(MaxSeq - 1)]

ElemSet(s) == { s[i] : i \in 1..Len(s) }

IsUnique(seq) == \A i, j \in 1..Len(seq): i # j => seq[i] # seq[j]

\* EVOLVE-BLOCK-START
(* --algorithm HardQueueAlgo

\* EVOLVE-BLOCK-END

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

====


