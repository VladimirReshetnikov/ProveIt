# Conditional unscaled source to a positive trace75 zero

`Trace75UnscaledReverseGraph.graph_zero_of_source` is author-checked in every
IΣ₁ model. For natural ports p with beta positive, a positive natural source
valuation v, the explicit mask and natural transport equations, an index
`rankNat=2r+1` with r>0 and the stated phase, `X=2^(2r+1)`, `72r<X+1`, and
positive unscaled first-Pell interval witnesses satisfying the two displayed
coordinate equations, it constructs a positive valuation at which the actual
trace75 ring value is zero. The proof binds one unscaled reverse-data tuple to
the actual rank, E, old V, carrier Z and remaining registers, then uses the
positive natural parts theorem. It does not export coordinate equalities for
the final valuation as part of the theorem conclusion.

This is conditional model-level graph construction. It does not show that BFS
halt supplies its source hypotheses, prove a halt iff or iPRA theorem, or bind
external coefficients. Accepted exploratory author check
`observations/data-attempt04/` produced
`/tmp/trace75-unscaled-graph-ya6xqo8t/Trace75UnscaledReverseGraph.olean`
SHA-256 `50e65bb13f008d7efd3e6e4b9806251bdd87014e88e8e714aa92b51631aad6a3`.
Attempts01–03 are retained failures: namespace shadow, register/cast goals,
and a warning-only runner rejection, respectively.

The accepted run uses a guarded **old-first mixed namespace overlay**. Its
`observations/overlay-attempt01/result.json` records 1,506 old and 998 fresh
files, 997 shared paths and five byte-different objects:
`ArithmeticCarrierRadix2011`, `ArithmeticCarrierSoundness2011`,
`ArithmeticNegativeNorms`, `ArithmeticWindowInterface`, and `ModelRatioBounds`.
Old objects win on shared paths and fresh files fill missing paths. Both input
inventories and selected targets/hashes are rechecked before and after the
run; its two direct imports are pinned. This is not a coherent provider-closure
or source-ancestry proof. Historical producer drift, package and dynamic
ancestry remain inherited; this result has not been transferred to the fresh
trace75/BFS union.
Independent source and receipt audit passed in
`reviews/trace75-unscaled-reverse-graph-independent/`; no Lean replay was done.
