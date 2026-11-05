# Free-carrier proof plan: the main index is at least six

The free main carrier appears sufficient to derive `m≥6` at compact44-size
ports **without** the missing first-index congruence. The argument below is a
standard-integer proof and a model-level Lean plan. It is conditional on the
stated root/carrier, q-scale and size hypotheses; no Lean lemma or actual
compact44 extraction is claimed by this packet yet.

Let positive natural-model values satisfy

```
q≥33,  X≥q,  Y≥3,  U=Y²,  a=XY+Y,  H=4a+3,
g=xcoord m a,  c=ycoord m a,
U g=U(X+a c)+H h.
```

Only these explicit assumptions are needed below; `q³|Y` is a stronger
hypothesis available in the 72 graph. At compact44 ports `q≥47`; its graph
coordinates also give `X≥q` and `Y≥3`. Actual graph-level extraction of all
those facts remains a separate proof obligation.

## Projection and gcd

The existing [`projection_quotient`](../../Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean)
gives a natural `z` with

```
g = 2^m + a c + H z.
```

Substitution in the free carrier, followed by reduction modulo positive `H`
and cancellation of the common additive term `U a c`, gives

```
(U·2^m) mod H = (U·X) mod H.
```

Apply [`P72Mu.gcd_cancel`](../../Lean/DiophantineConsistency/Compact44/P72Mu.lean)
with arguments `(H,U,2^m,X)`. It returns positive `e,mu` with
`H=e mu`, `e|U`, and `2^m ≡ X (mod mu)`. As `e|U=Y²` and `e|H`,
[`P64Early.gcd_dvd_nine`](../../Lean/DiophantineConsistency/Compact44/P64Early.lean)
gives `e|9`, hence `e≤9` and `H≤9mu`.

Since `Y≥3` and `X≥q≥33`, `H=4(X+1)Y+3>9X`; consequently `X<mu`.
If `m≤5`, then `2^m≤32<q≤X<mu`. Both sides of the modular equality
are already below `mu`, so it forces `2^m=X`, a contradiction. Therefore
`m≥6` in the standard integers.

The model-level proof can use the exact same existing gcd and projection
lemmas, `Exp.exp` monotonicity for `m≤5`, and order cancellation. Its result
must be checked in Lean before it is asserted for arbitrary nonstandard
`IΣ₁` models. Combined with the separate `ycoord 6` identity/monotonicity,
`m≥6` would supply `(a+2)delta(a)²<c`. Together with the conditional rank
half-window, the strong and auxiliary residuals could then meet the
signed-half-index theorem's size hypotheses. That would establish `m=R`
only after those residuals and the actual compact-port window are also
extracted; the old first-index congruence and 72→76 reverse still remain.

[`check.py`](check.py) pins the relevant source lemmas and tests 4,080
q-cube parameter tuples and all six indices `m=0,…,5`; it observes all three
possible gcds 1, 3 and 9. These are finite controls, not a proof of the
universal statement. Run with `python3 -I -S -B check.py`.
