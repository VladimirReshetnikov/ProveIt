# Physical packing transport without mask hypotheses

`CompactPartialPackingTransport.lean` factors the transport part of
`ArithmeticPacking` through a smaller `TransportInput`. For a
Σ₁-definable model cell family `X`, its exact premises are:

* `1 < N` and `s < N`;
* `K * X j < 2^d * 2^d` for `j < N`;
* `X j + blk d K N s X j < 2^d` for `j < N`;
* `1 ≤ X 0`.

The theorem proves that the cyclic remainder of
`(K + 2^(d*s)) * Cw d N X` modulo `2^(d*N)-1` is exactly the represented
normalized block word `Fw d K N s X`. In particular it proves `Fw` is
strictly below that modulus using the positive source origin and the
cell-plus-block bound. It does **not** assume `PackingInput`, positivity of
the origin block, either low mask, or either high mask. This avoids using
the high-mask conclusion as a premise when joining the transport identity to
the carry-free stencil theorem. The result alone does not prove a high-mask
condition, graph zero or internal iPRA theorem.

The first bounded attempt checked the transport identity but failed on a
local source-word positivity rewrite and reported three unused-instance
warnings; its source and compiler output are retained in
`observations/attempt01`. The corrected bounded single-author run, tool
session `20058`, exited 0 without warnings or `sorryAx`; both named axiom
reports list only `propext`, `Classical.choice`, and `Quot.sound`. The direct
dependency and complete selected overlay guards were unchanged; the
word/controller provider overlap check found no conflicts. The command,
source/object hashes, dependency listing, compiler log and full preflight
are in `observations/attempt02`.

This is a mixed-provider author-side build, not a paired replay or a fully
authenticated dependency closure. Package, transitive, dynamic-loading and
between-observation ancestry remain inherited.
