# Adaptive rank window from an actual zero

`ArithmeticAdaptiveRankWindow2011` establishes the rank window in every
`IΣ₁` model from the actual adaptive equation, prior to any index relation
or representation of an input as a power. For shifted positive inputs `v`,
write `q = 1+v₀β` and

```
R = ((q−1)(q−v₁)+v₂)(q²−1) + (MC+q·MF)v₀.
```

The module proves `24 ≤ R` and `R+q³+q+1 ≤ q⁴`; the current natural client
assumes only that the literal 13-variable expression evaluates to zero.
The source's fourth port `MF` is already shifted once: `highPort+β`.
The gap `v₁+v₂<q` is derived from the first carrier, while the mask bounds
are proved for the actual current constants. The upper bound is witnessed
by an explicit additive slack identity, so it does not use signed subtraction
or standard-model induction for an internal variable.

This is a window for the rank expression, not a proof that it equals the main
Pell index. The adaptive proof still needs the signed main-root congruence
`q⁴ | (k−R−1)` (or an equivalent additive statement), factor-three
cancellation for arbitrary internal `q`, and the index comparison and strong
norm steps. In particular no divisibility of `X` by `q`, power representation,
or index offset is assumed here. The target expression agrees with the one
used in the main-root orientation after rewriting `q−1=v₀β`.
