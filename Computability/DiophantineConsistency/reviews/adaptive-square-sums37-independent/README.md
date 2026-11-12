# Independent review: 37-variable zero-only quartic reduction

The [37-variable candidate](../../research/adaptive-square-sums37-difference-quartic/README.md)
and this separate exact checker reproduce. The domain, residual identities,
operation counts and standard-integer zero-map argument agree with the
proposal. This is an external mathematical/source review; no Lean model proof
or new iPRA endpoint has been established.

The positive child has **37 positive inputs**, 158 live binary operations and
28 squared residuals. The separate graph shifting each input by one has **37
nonnegative inputs** and 195 live operations. Both have exact degree four:
every child residual is at most quadratic in the unknowns, and the output's
`firstQuotient⁴` coefficient is one independently of the four ports. The
checker validates the actual sum chain and that each square occurs once.

The child replaces parent `squareVariable` and `ySquareVariable` by a single
positive `differencePlusOne`. The old square-defining residuals disappear, and
its new residual is

```text
E = (differencePlusOne - 1) - (y² - v²).
```

After restoring the two parent coordinates as `v²` and `y²`, all other
residuals agree except the auxiliary one; exact sparse polynomial arithmetic
verifies `parentAux = childAux + Q*E`. Thus a positive child **zero** lifts
to a parent zero: its `E` is zero and `v²` and `y²` are positive. The outputs
are not identical at arbitrary points. For example, with all four ports and
all child inputs equal to one except `differencePlusOne = 2`, the lifted
parent output is 757 and the child output is 759. The correspondence is a
zero-set equivalence, not the stronger polynomial equality used in QM38.

For the other direction, at a positive parent zero the square constraints and
auxiliary residual give `Q*(y²-v²)=y²-1`. Here `Q>0` and `y≥1`, so
`y²-v²≥0`; define the positive child value as `y²-v²+1`. This maps parent zeros
to child zeros and reverses the lift. The reasoning does not rely on a sign
assumption for the fixed integer ports.

The same ordered argument is mathematically applicable in the intended
nonstandard IΣ₁ models: use the ordered difference ring, positivity of the
embedded Q, and `y²≥1` to reflect `v²≤y²` back to the natural-model order.
That order supplies a model-natural `d` with `v²+d=y²`; use `d+1` for the
child coordinate. This requires the stated ordered-embedding, product-sign and
additive-decomposition facts and a Lean proof that sum-of-squares zero gives
each model residual zero. This review does not assert those proof scripts or
providers compile.

The parent is the separately reviewed QM38 reduction of the 40-variable
current-2011 graph. Its proposed IΣ₁ transfer is also unelaborated. Composing
with a compatible checked parent endpoint, verifying axiom closure, and binding
any physical PDF remain separate. The reduction trades variables/operations for
degree against the compact natural-79 graph; it is not a global minimum.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-square-sums37-difference-quartic/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-square-sums37-difference-quartic/result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/adaptive-square-sums37-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/adaptive-square-sums37-independent/result.json
```
