# Typed polarity lemmas for the dual translation

`PA194DualComplement.lean` proves local polarity facts for the paired NNF
translation components. In candidate-PRA models whose arithmetic reduct also
satisfies IΣ₁, the explicit truth, membership, and equality code pairs are
pairs of a Foundation typed formula and its typed negation. The implication
constructor preserves this polarity for arbitrary typed input formulas. The
quantifier wrapper preserves it when the supplied closing code maps the two
input polarities to an already complementary pair of closed bodies.

These are local typed-syntax lemmas, not a global invariant over the
recursive source translator. The assumed behavior of the closing code is not
proved, the exceptional zero implication alias remains separate, and neither
PA calibration nor an iPRA machine-consistency equivalence follows. The
corresponding numeric code equations in the component files hold in all
candidate-PRA models without assuming IΣ₁; these Foundation typed-syntax
identifications and polarity statements explicitly assume IΣ₁.

Rebuild with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-dual-complement.sh
```
