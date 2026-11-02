# Exploratory clean-phase neighbors

For any IΣ₁ model, `CleanPhaseNeighbors.model_neighbors` proves that if model x<8807 lies outside the compact blocker B, the cyclic phase predecessors `cyc 8807 x 1` and `cyc 8807 x 2` are not 1063. The proof reduces bounded model x to a standard numeral, uses a symbolic Lean arithmetic certificate and transports the result through the model cyclic-index/cast interface. It does not use the external Python check as a model proof.

The fresh rotation-pair author overlay and seven-source rebuild from commit 9403a827c7 were used. Two additional exact geometry sources were rebuilt in outer session 6395 (exit 0, both children exit 0 without warnings or `sorryAx`). Client session 15610 actually exited 0 without warnings or `sorryAx`, with reports `propext`, `Classical.choice`, `Quot.sound`. Failed sessions 27188 and 42741, their sources and logs are retained; their `sorryAx` diagnostics prove nothing. This is single-side exploratory evidence, not a paired replay or independent artifact audit.

The theorem concerns phase predecessors only. Transport from full-word cyclic indices to these phases, the fractional temporal half-radix bound, a clean carry or graph column, retained K binding and internal iPRA remain open.
