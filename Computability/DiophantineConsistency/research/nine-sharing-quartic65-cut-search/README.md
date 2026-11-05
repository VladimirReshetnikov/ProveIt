# Bounded cut search for the sharing-aware quartic seed

This deterministic 5,000-iteration local search explores degree-feasible materialization cuts for the signed-pair encoding of the current 65-operation graph. It uses a fixed random seed, repairs a proposed cut set whenever a pair component would exceed degree two, then prunes unnecessary cuts. Its best result uses 38 materialized gate witnesses plus the 14 original inputs, improving the 54-witness baseline to 52. It visited 80,231 distinct cached cut sets. This is a heuristic search, not an exhaustive proof or a global lower bound.

A result of the degree model alone is not a seed proof. The separate [52-witness candidate](../nine-sharing-quartic65-52-candidate/README.md) constructs the exact residual AST and checks its identities, fixed bytes, residual degrees, witness assignments and normalization. Neither packet claims a Lean model bridge, Jones proof or iPRA endpoint.
