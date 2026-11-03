# Population bound from an actual 80-graph zero

`Direct80PopulationModel.graph_population` proves in every IΣ₁ model: for a positive zero of the 80-operation graph, β ≥ 31, odd β, symbolic low/high port bounds, d ≥ 2 and β+1=2^d, there is a positive internal N such that `J=rep d N` and `3*d*N+2 ≤ population(rankNat)`. Both scaled and shifted Pell sandwich inequalities are supplied by `Direct80SandwichBoth.graph_sandwich_both` at the **same** r, and the checked rounding lemma derives the required half-binomial identity. Neither a sandwich nor a half-binomial identity is assumed by this theorem.

This is a model-theoretic population bound, not yet graph-to-halt soundness, a converse, iPRA provability, or literal-payload/PDF binding. The theorem has symbolic-port and radix assumptions; specializing them requires additional checked connections.

The fresh author check `observations/populationmodel-attempt01/` exited 0 without diagnostics. Its printed axioms are `propext`, `Classical.choice`, `Quot.sound`; object `/tmp/tenpositive-80populationmodel-6pbzkhxv/Direct80PopulationModel.olean` has SHA-256 `e2462f9250872ab363da4b93ac6661c788835ba91cfd62bd8fc54a4a86bbee22`. The guarded runner pins selected project objects and resource samples; the inherited source/object, package and dynamic ancestry have not been independently authenticated. This is not an independent Lean replay.
