# High-mask safety for compact field intervals

`CompactWordFieldHigh.lean` proves actual physical-block no-carry against the
symbolic high mask for every model phase in either interval
`1013 ≤ p < 1023` or `1065 ≤ p < 1074`. It assumes a marked `CompactWord`,
`1<N`, `s<N`, definable row and dummy functions, Boolean dummy inputs and an
in-range cell index. It does not assume any high-mask safety or full packing.

The proof reduces the bounded model phase to a standard numeral, applies the
previously checked physical field or marker evenness theorem, and uses the
fact that each corresponding symbolic high-mask digit equals one. Thus these
19 field/marker phases satisfy their exact local `NoCarry` obligations. It
does not establish the origin, anchor, target or padding classes, full
high-mask safety, graph zero, or an iPRA theorem.

The first two guarded author attempts failed on dependent substitution and
then on numeral-cast normalization in the two marker cases; their exact
sources and logs are retained. The corrected third attempt, session `3178`,
exited 0 without warnings or `sorryAx`, with unchanged sampled direct
import/companion, selected provider-root and mixed-overlay guards. Both named
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The command, source/object hashes, dependency scans, logs and inventories are
retained. Provider package, transitive, dynamic and between-observation
ancestry remains inherited; `/tmp` paths are ephemeral. This is not a paired
replay or a complete dependency-closure audit.
