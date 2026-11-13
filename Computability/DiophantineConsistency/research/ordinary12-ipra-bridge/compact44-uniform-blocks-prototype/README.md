# Uniform parameterized block packing

`UniformBlocks.lean` proves that if a ternary model function `f a b j` is
Σ₁-definable and all its values are less than `2^w`, then the represented
block sum `bsum w (f a b) n` is Σ₁-definable uniformly in the two parameters
`a` and `b`, for fixed model `w` and `n`. The graph expresses the existing
`Blocks` predicate directly; `bsum_graph` supplies its equivalence with the
chosen block sum under the stated uniform bound. The proof is in models of
`IΣ₁`, not itself an object-theory iPRA derivation.

The guarded single-author run exited 0, with unchanged sampled direct
object and companion guards, no warnings or `sorryAx`, and the axiom report
`propext`, `Classical.choice`, `Quot.sound`. The runner, direct dependency
list, log and terminal record are retained in `observations/attempt01/`.
The provider's transitive and package ancestry is inherited. This lemma does
not itself construct the compact cell, the entire computation word, mask
safety or a compact equation endpoint.
