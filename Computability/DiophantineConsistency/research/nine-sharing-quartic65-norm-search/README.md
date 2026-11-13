# Five-norm degree-feasible cut search

A deterministic 5,000-iteration heuristic explores signed-pair materialization cuts for the first 60 rows of the current 65-gate graph, taking the five norm factors as terminal constraints. Its best examined result uses 24 materialized gate coordinates plus 14 shifted inputs, for 38 witnesses. The search is not exhaustive and proves no lower bound. The separate [norm38 candidate](../nine-sharing-quartic65-norm38-candidate/README.md) constructs and checks the actual residuals; neither packet is a Lean model bridge or iPRA proof.
