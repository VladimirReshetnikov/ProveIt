# Carry-free aligned symbolic stencil

`CompactAlignedStencilZeroCarry.lean` combines the exact symbolic cyclic
product carry input, the checked compact stencil mass, and the aligned
temporal-rotation theorem. For any bounded source word whose radix-`2^67`
digits are Boolean, and any temporal exponent of the form `67*e`, the
cyclic carry at every in-range column is zero and the corresponding digit of
the exact symbolic remainder equals its raw stencil column sum.

The second theorem constructs these hypotheses for every represented packed
cell word at positive length, for arbitrary supplied Σ₁-definable row and
dummy functions. It needs no `CompactWord`, high-mask or graph-zero
assumption. It concerns the global remainder of `(K + 2^(67*e))*C` modulo
`2^(67*n)-1`; it does **not** by itself identify that remainder with the
physical `blk` word or prove that its raw columns satisfy the high mask.
Nor does it establish a graph zero, retained-byte binding or iPRA theorem.

The bounded single-author build, tool session `40269`, exited 0 without
warnings or `sorryAx`; both named axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`. The source/object hashes, command,
dependency listing, compiler log and unchanged sampled direct dependency and
companion guards are retained in `observations/attempt01`. The prior
temporal, word, coefficient and provider package, transitive, dynamic-loading
and between-observation ancestry remain inherited. This is not a paired
replay or a complete independently authenticated closure.
