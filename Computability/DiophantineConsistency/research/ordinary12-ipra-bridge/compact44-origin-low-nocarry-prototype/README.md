# Low-mask no-carry at the compact word origin

`CompactOriginLowNoCarry.lean` proves
`NoCarry (packedCell 0 0 - 1) (CompactConcreteIncrement.mask + 1)` in every
model of IΣ₁. The row-zero, zero-dummy cell has its low bit set and the
concrete mask has its low bit clear. The general `swap_origin_bit` lemma
shows that moving that bit from the cell to the mask preserves their existing
no-carry property. This supplies the **special origin** low-mask condition
for a base word whose origin row is zero; it does not alone construct such a
word or establish any product, high-mask or graph-zero condition.

The first attempt failed while simplifying the concrete bit values and hit
the configured heartbeat limit; its source and compiler output remain in
`observations/attempt01`. The corrected bounded single-author run, tool
session `6406`, exited 0 without warnings or `sorryAx`. All three named axiom
reports contain only `propext`, `Classical.choice` and `Quot.sound`. Direct
dependency and companion guards were unchanged; the command, source and
object hashes, dependency list and compiler log are in
`observations/attempt02`. The base low-mask and its other providers' package,
transitive, dynamic-loading and between-observation ancestry are inherited;
this is not a paired replay or a fully authenticated dependency closure.
