# Strict graph cut: source specification

This is a local Foundation adaptation of the vendored `RelationalGraphRestriction.lean` from PA196. `strictEntry top p` says p is an ordered-pair object whose first coordinate is in top; `strictGraphCut top g h` specifies h by filtering the actual entries of g using that property. `strictCutExists` is a source natural-deduction proof that the explicitly supplied parameterized Separation instance gives a strict-cut witness. `strictEntryIntro` and `strictEntryEliminate` construct and eliminate the coordinate witnesses.

The Separation instance remains an explicit source-proof input here. The module does not yet prove edge characterization, the seven order-bijection clauses, successor cancellation or an iPRA result.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-foundation-graph-restriction.sh "$PWD" /dev/shm/pa194-foundation-graph-restriction-repo-NEW` at the repository root. The checker compiles this adaptation in a fresh output against hash-pinned prebuilt dependencies, including the repository-replayed subgraph support and unified PairGraph syntax. The successful output is `/dev/shm/pa194-foundation-graph-restriction-replay`.
