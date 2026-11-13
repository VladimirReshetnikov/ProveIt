# Exact high-mask safety at the two target phases

`CompactMarkedTargetHighNoCarry.lean` proves that, at every valid cell of a
supplied compact word with globally Boolean dummy values, the actual
normalized block digit has `NoCarry` against the corresponding **exact
symbolic `highNat` digit** at both local phases 4393 and 5495. The other
assumptions are Σ₁-definability of the row and dummy functions, `1 < N` and
`s < N`. No high-mask no-carry premise or complete `PackingInput` is used.

The proof joins the new exact block-digit values `1 + 2^51` to the existing
finite fact that this value is disjoint from `2^51 - 2`, and to the checked
model identities giving that value for both symbolic high-mask digits. It
does not prove safety at the field, anchor or padding phases, a complete
high-mask condition, a graph zero, retained-byte binding or an iPRA theorem.

The existing occupied-value no-carry module was rebuilt as an object from its
unchanged source. Single-author tool session `72842` exited 0 without
warnings or `sorryAx`, with unchanged sampled direct dependency guards. Its
source, runner, dependency list, compiler log and terminal receipt are
retained under `occupied-rebuild/`; the rebuild is not an independent replay.

The final bounded single-author join, tool session `61800`, exited 0 without
warnings or `sorryAx`; its named axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. Direct dependency guards, the full
selected project union overlay and selected controller, symbolic-kernel and
static-mask root inventories were unchanged. Provider-overlap comparisons,
selected inventories, source/object hashes, command, dependency listing,
log and terminal receipt are in `observations/attempt01`.

This is a mixed-provider author-side result, not a paired replay or a fully
authenticated dependency closure. Package, transitive, dynamic-loading and
between-observation ancestry remain inherited.
