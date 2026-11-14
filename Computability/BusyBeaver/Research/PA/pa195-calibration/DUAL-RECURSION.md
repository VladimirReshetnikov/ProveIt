# PA194 recursive positive/negative translation skeleton

`PA194DualRecursion.lean` combines the primitive-recursive history, the exact
PA194 tag and child decoders, and the explicit dual truth, membership,
equality and implication codes. Each translated source formula is represented
by a bare pair `(positive, negative)` of numeric negation-normal-form syntax
codes. Negating the fixed bit template is done at Lean code-construction time,
and implication uses `Or(left.negative,right.positive)` for its positive part
and `And(left.positive,right.negative)` for its negative part. No generic
runtime formula-negation operation is needed.

In every candidate-PRA model, including nonstandard source codes and labels,
the supplied decoder and pair-projection certificates imply the exact numeric
zero, membership, equality, nonzero implication, and universal recursion
equations. Suitable decoder and projection certificates are known to exist;
their particular PR code numerals are not fixed here. For universal formulas,
the paired binder-closing operation is still a supplied binary code: it has
not been constructed or certified. It receives the second decoded field as
binder and the first child's recursively translated pair as body.

This is not yet a verified PA translation. It does not prove the positive and
negative syntax codes' recursive semantic duality, the exceptional zero
implication alias's logical equivalence, universal binder correctness, PA
calibration, machine internalization, or either consistency implication.
The numeric equations do not assume IΣ₁; separate Foundation named-syntax
identifications in the component files have explicit IΣ₁ assumptions.
Rebuild with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-dual-recursion.sh
```
