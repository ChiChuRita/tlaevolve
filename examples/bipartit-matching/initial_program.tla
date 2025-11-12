---- MODULE BipartiteMatching ----
\* EVOLVE-BLOCK-START
EXTENDS Naturals, FiniteSets, TLC, Sequences

\* Problem: Bipartite matching with optimality certificate (minimum vertex cover)
\* Inputs are modeled as constants so TLC can instantiate different graphs via tlc_config.cfg
CONSTANTS LeftNodes, RightNodes, Edges

EdgeSet == LeftNodes \X RightNodes

(* --algorithm BipartiteMatching {

variables
  match = {},
  coverLeft = {},
  coverRight = {};

{
  Compute:
    \* Compute a maximum matching and a minimum vertex cover atomically
    match :=
      LET
        IsMatching(m) ==
          /\ m \subseteq Edges
          /\ \A l \in LeftNodes:
                Cardinality({ r \in RightNodes : <<l, r>> \in m }) \leq 1
          /\ \A r \in RightNodes:
                Cardinality({ l \in LeftNodes : <<l, r>> \in m }) \leq 1
        AllMatchings == { m \in SUBSET Edges : IsMatching(m) }
      IN CHOOSE m \in AllMatchings:
           \A mm \in AllMatchings : Cardinality(mm) \leq Cardinality(m);

    coverLeft :=
      LET
        AllCovers ==
          { p \in (SUBSET LeftNodes \X SUBSET RightNodes) :
              \A e \in Edges: LeftOf(e) \in p[1] \/ RightOf(e) \in p[2] }
        chosenCover == CHOOSE p \in AllCovers:
                          \A q \in AllCovers :
                            (Cardinality(p[1]) + Cardinality(p[2])) \leq (Cardinality(q[1]) + Cardinality(q[2]))
      IN chosenCover[1];

    coverRight :=
      LET
        AllCovers ==
          { p \in (SUBSET LeftNodes \X SUBSET RightNodes) :
              \A e \in Edges: LeftOf(e) \in p[1] \/ RightOf(e) \in p[2] }
        chosenCover == CHOOSE p \in AllCovers:
                          \A q \in AllCovers :
                            (Cardinality(p[1]) + Cardinality(p[2])) \leq (Cardinality(q[1]) + Cardinality(q[2]))
      IN chosenCover[2];

  Finish:
    skip;
}
} *)
\* EVOLVE-BLOCK-END

\* Helpers
LeftOf(e)  == e[1]
RightOf(e) == e[2]

\* Sanity about the given graph
GraphOK ==
  /\ Edges \subseteq EdgeSet
  /\ IsFiniteSet(LeftNodes) /\ IsFiniteSet(RightNodes)

\* Invariants and properties over program variables
TypeOK ==
  /\ match \subseteq EdgeSet
  /\ coverLeft \subseteq LeftNodes
  /\ coverRight \subseteq RightNodes

\* Matching has no shared endpoints
NoSharedEndpoints ==
  /\ \A l \in LeftNodes:
       Cardinality({ r \in RightNodes : <<l, r>> \in match }) \leq 1
  /\ \A r \in RightNodes:
       Cardinality({ l \in LeftNodes : <<l, r>> \in match }) \leq 1

\* The matching must use only graph edges
MatchingSubsetOfGraph == match \subseteq Edges

\* Vertex cover checks
EdgeCovered(e) == LeftOf(e) \in coverLeft \/ RightOf(e) \in coverRight
CoverHitsMatchingEdges == \A e \in match: EdgeCovered(e)
CoverHitsAllEdges      == \A e \in Edges: EdgeCovered(e)

\* Size equality (Kőnig's theorem certificate)
SizeEquality == Cardinality(match) = Cardinality(coverLeft) + Cardinality(coverRight)

\* Initial condition sanity (optional)
InitialConditionOK ==
  Init => /\ match = {}
          /\ coverLeft = {}
          /\ coverRight = {}

\* Goal states: a valid certificate of optimality was found
ValidCertificate ==
  /\ NoSharedEndpoints
  /\ MatchingSubsetOfGraph
  /\ CoverHitsAllEdges
  /\ SizeEquality

ReachGoal == <>ValidCertificate

\* Encourage fairness in the synthesized Next
FairSpec == Spec /\ WF_vars(Next)

====