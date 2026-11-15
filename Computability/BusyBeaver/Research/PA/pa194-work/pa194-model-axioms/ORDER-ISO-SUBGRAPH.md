# Subgraphs preserve order-bijection clauses

In Foundation natural deduction, `subsetImpliesEdgeSubgraph` proves that set inclusion h ⊆ g implies that every edge of h is an edge of g. The edge-subgraph formula is definitionally equal to the existing `PairGraph.inclusion` formula. `functionalSubgraph`, `injectiveSubgraph` and `orderSubgraph` prove that edge inclusion transfers the functional, injective and order-preserving clauses from g to h. These statements use no additional nonlogical axioms; the inclusion and original graph clauses are explicit premises.

This establishes three clauses needed after constructing a restricted graph. It does not construct a separating subset or establish the graph's entries, typing or totality, nor successor cancellation or the native iPRA equivalence.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-order-iso-subgraph.sh "$PWD" /dev/shm/pa194-order-iso-subgraph-repo-NEW` from the repository root. The checker compiles the module against hash-pinned prebuilt dependencies, including the repository-replayed greatest-image support and unified PairGraph syntax. The successful output is `/dev/shm/pa194-order-iso-subgraph-replay`.
