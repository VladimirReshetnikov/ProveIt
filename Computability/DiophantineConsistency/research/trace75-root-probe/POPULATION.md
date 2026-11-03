# Trace75 population bound

`Trace75Population.graph_population` proves in any IΣ₁ model with β≥31,
`MC<β`, `MF<2β`, a positive trace75 zero, `d≥2`, and `β+1=2^d` that
one positive `N` satisfies `J=rep(d,N)` and
`3*(d*N)+2≤population(rankNat)`. The port `K0` is arbitrary. The proof
extracts the half-binomial identity from both shifted Pell inequalities,
uses the same repunit length `N` and the actual cubic factor in `Y`, and
applies the binary population lemma. This is a necessary model condition,
not a machine-halt or iPRA equivalence.

`run-population.py`, `observations/population-attempt01/`: Lean exit 0,
no warning/error; object
`/tmp/trace75-population-wjnqz5r8/Trace75Population.olean`, SHA-256
`489720787a2df7640be88dc68768b1b62a9e9e3d7172128fe246c90a13f20332`.
Selected direct providers and first-resolved historical `ModelRatioBounds`
are pinned; known producer-time drift, a coherent fresh-provider rebuild,
full transitive/package provenance and graph/file binding remain open.
