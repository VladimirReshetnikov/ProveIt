# Positive and negative truth and atomic syntax codes

`PA194DualAtomCode.lean` constructs explicit primitive-recursive pairs of
positive and negative codes for truth, the fixed binary membership formula,
and equality. The negative bit formula is negated once at source-code
construction time, so using the code does not require a generic recursive
formula-negation function. The equality code uses the actual Foundation
free-variable vector encoding.

In every candidate-PRA model, including at nonstandard variable labels,
the numeric equations hold without IΣ₁. Separate theorems identify the
resulting values with Foundation's internal truth/falsity, instantiated bit
formulas and positive/negative equality atoms in IΣ₁ models. The static
negated bit formula's numeric code is large and is not serialized here.

This is a component of a proposed positive/negative translation; it does not
establish its recursive invariant, universal binder closing, PA calibration,
or a machine-consistency reduction. Rebuild with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-dual-atom-code.sh
```
