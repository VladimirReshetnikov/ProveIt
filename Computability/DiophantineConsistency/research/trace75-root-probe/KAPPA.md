# Positive trace75 projection quotient

`Trace75Kappa.graph_positive_kappa` proves in every IΣ₁ model with β≥31,
`MC<β`, `MF<2β`, and an actual positive trace75 zero that there is a
positive natural `kappa` with signed graph equality `K=H*ι(kappa)`.
`K0` is arbitrary. It uses the unweighted signed divisibility and positivity
of the actual graph `H` and `K`, then proves the signed quotient has a
positive natural representative. It does not yet bind a source-graph
valuation or prove machine halt/iPRA equivalence.

Accepted `run-kappa-v2.py`, `observations/kappa-attempt02/`: Lean exit 0,
no warning/error; object `/tmp/trace75-kappa-2u56dkuh/Trace75Kappa.olean`,
SHA-256 `d1b5f11393d947960986f70e247db55dbcc559a4fe7214878006f64a25f78b2a`.
Attempt 01 is retained: it failed to eliminate a contradiction into an
existential and reported `sorryAx`. Selected direct imports and the
first-resolved historical `ModelRatioBounds` are pinned; its producer-time
drift, coherent fresh-provider rebuild, full transitive/package provenance
and external graph/file binding remain open.
