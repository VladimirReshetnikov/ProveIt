# Uniform definability of compact cells

`CompactUniformPackedCell.lean` defines `normalizedCell a d` to be the
previously constructed `packedCell a (d % 2)`. Using uniform definability of
the ternary digit function and `UniformBlocks.bsum_uniform`, Lean proves that
this normalized cell is a Σ₁-definable function of **both** model parameters.
The normalization guarantees bounded digits for all parameters; for `d ≤ 1`,
the normalized cell equals the original fixed-parameter cell. A further
client proves that composing it with any two Σ₁-definable model functions
gives a Σ₁-definable cell word and that all its cells are below
`2^(67*8807)`, without assuming that the input dummy function is Boolean.

This gives a definable cell family from supplied row and dummy functions. It
does not select or construct those functions, prove the needed properties of
an actual compact word, establish either mask or pulse safety, prove
`PackingInput` or graph zero, or produce an internal iPRA derivation. When the
supplied dummy value is Boolean, the earlier selector, payload-copy, dummy,
and row-zero positivity lemmas transfer through `normalizedCell_eq`.

The bounded single-author build, tool session `35135`, exited 0 without
warnings or `sorryAx`. All four named axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`; the direct dependency and companion
guards were unchanged. The dependency listing, compiler log, source hash,
command, output object hash, and terminal receipt are retained under
`observations/attempt01`. This result inherits the previous packed-cell,
uniform-block, and digit providers' transitive, package, dynamic-loading, and
between-observation ancestry limitations. It is not a paired replay or a
complete independently authenticated dependency closure.
