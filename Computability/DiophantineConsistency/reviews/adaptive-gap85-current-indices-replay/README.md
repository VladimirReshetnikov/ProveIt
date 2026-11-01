# Actual fixed-port 85-zero combined Pell-index bounds

Both source-directed replays PASS with two matching source/object/full-log rows, zero warnings and standard Lean axioms. In every IΣ₁ model, `AdaptiveGap85CurrentIndices.current_zero_index_bounds` proves that any actual positive literal 85-zero at the current fixed ports has Pell witnesses with first index n≥3, main index m≥5, n<m, and the stated coordinate identities. It is a necessary condition, not a proof of no zeros or of the 85-operation equivalence.

Input and driver: `research/adaptive-gap85-normalization/AdaptiveGap85CurrentIndices.lean` and `replay_current_indices.py`. The replays pin 401 selected project-object/companion paths on the independently replayed first-index-three provider; original project and external package transitive source ancestry remains historical.
