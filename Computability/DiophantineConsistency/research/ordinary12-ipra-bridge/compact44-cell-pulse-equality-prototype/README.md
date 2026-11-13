# Equality of normalized dummy cells and explicit pulses

`CompactCellPulseEquality.lean` proves that replacing the zero dummy digit by
one adds exactly `2^(67*1063)` to the represented compact cell. Consequently,
for arbitrary model parameters,

```
normalizedCell a d = packedCell a 0 + 2^(67*1063) * (d % 2).
```

This directly connects the uniformly definable cell used in the represented
word to the explicit dummy pulse used in the packing/rank construction.
The point-indicator block-sum proof follows the existing
`ArithmeticControllerDataCompact44.bsum_pt` and `bsum_add_pt` proofs; the
source records that attribution. The theorem does not establish pulse
support away from the origin, product/high-mask conditions, graph zero or an
iPRA proof.

The guarded single-author compile exited 0 without warnings or `sorryAx`,
with unchanged sampled direct dependency and companion guards. Both named
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The runner, source/object hashes, compiler log and terminal receipt are
retained. Provider transitive, package, dynamic and between-observation
ancestry remains inherited; `/tmp` paths may disappear.
