# Independent review: 36-variable combined-shift quartic

The [36/155 candidate](../../research/adaptive-square-sums36-combined-shift-quartic/README.md)
and this independent checker reproduce. The source DAG edits, squared-residual
identities, quartic degree and the stated beta-qualified positive zero maps
check externally. No Lean model proof or new iPRA endpoint is established.

The positive graph has **36 positive inputs, 155 live operations and 27
squared residuals**; its explicit input-shift graph has **36 nonnegative
inputs and 191 live operations**. Every residual has degree at most two, and
`firstQuotient⁴` has coefficient one in the total sum, so the exact degree is
four for every integer specialization of the ports. Both graph schedules are
acyclic and all inputs, ports and operations are live.

The reduction replaces the positive parent inputs `productVariable` and
`gammaProductVariable` by one `combinedShift`. It restores them as
`productVariable2*(1+J*beta)` and `mainScaleVariable*gamma`. The checker
independently verifies the complete row edits, both sums of squares, and the
formal-port identities: both removed parent product residuals vanish under the
lift, the remaining unchanged residuals agree, and

```text
parent dDifference = child dDifference + H * combinedEquality.
```

At a positive child zero, `combinedEquality=0`, so this lift gives a parent
zero **provided beta is nonnegative**. Then `q=1+J*beta≥1`, so the restored
first product is positive; the second is positive from its retained positive
factors. At a positive parent zero, the two old constraints show the new
combined value is their sum, which is positive and satisfies the combined
constraint. These maps reverse each other on zeros. They do not assert equality
of outputs off zero: with all ports and child inputs equal to one except
`combinedShift=4`, the lifted parent output is 1361 and the child output 2209.
For negative beta the proposed lift can fail to preserve positivity: `J=1`,
`beta=-1` gives `q=0`. This is a limitation of the map, not a claim that the
equations are inequivalent for negative beta.

The fixed current-2011 source defines beta as the natural
`(2^47)^2011 - 1`, puts its integer cast in port zero, and states beta's
natural positivity. For an arbitrary IΣ₁ model the relevant safe interface is
an explicit equality between that port's cast in `DiffRing V` and the image of
a **model-natural** beta. Nonnegativity of that model value suffices, even if
it is zero; no model-positive-beta lemma is needed for the q bound. An existing
unelaborated natural-79 draft illustrates `Int.cast_natCast`/`map_natCast` for
a similar port. A checked cast lemma at the exact current ports, positivity
of the reconstructed model coordinates, all zero maps and endpoint transfer
remain to be produced; standard-integer `beta_pos` is not by itself a compiled
proof of those model statements.

The earlier [QM37 review](../adaptive-square-sums37-independent/README.md)
also uses a zero-only map, while the 40-variable endpoint has historical
single-author/provider limitations. Composition therefore remains an explicit
Lean obligation. This review does not establish a new iPRA derivation, physical
PDF binding or global minimum.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-square-sums36-combined-shift-quartic/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-square-sums36-combined-shift-quartic/result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/adaptive-square-sums36-combined-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/adaptive-square-sums36-combined-independent/result.json
```
