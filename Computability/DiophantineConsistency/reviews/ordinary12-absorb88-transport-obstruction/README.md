# A conditional obstruction to universal 88-row transport positivity

The other two residuals of the proposed 88-row graph cannot by themselves
force `Bt > 0`. Put `b = J*beta`, `q = b+1`, and

```text
G  = alpha + b*(q-F)
Bt = q*((q-F-alpha)*(K0+w)-F).
```

For any nonnegative integer `d`, replacing `F` by `F+d` and `alpha` by
`alpha+b*d` preserves `G` exactly and changes `Bt` to

```text
Bt' = Bt - q*(q*(K0+w)+1)*d.
```

The pinned 88-row DAG shows that, after cutting at `G`, neither the main
residual `A1` nor the ordinary residual `N` depends on `F`, `alpha`, `Bt`, or
the new first-root witness `r`. Thus this change preserves both residuals.

There is also a conditional *full-zero* construction over the standard
naturals. Assume a positive zero of the 89-row graph at the fixed ports. Its
already-checked first-root and transport results give positive integers
`first`, `Bt` and `b`, with `b ∣ Bt` and
`first² = 1 + ell*(ell+k)`. The fixed payload satisfies `K0 < beta²`; since
`q = J*beta+1` and `J ≥ 1`, it follows that `K0 < q²`.

Write `D = q*(q*(K0+w)+1)`, choose
`j = floor((Bt/b)/D)+1` and set `d=b*j`. Then `Bt' = -b*u` for an integer
`1 ≤ u ≤ D`. Replace the 88 graph's independent first-root witness by

```text
r' = first - (k*b+1)*u.
```

This witness is positive. Indeed, `k ≥ 2`, `q ≥ 2`, and `w,s ≥ 1`, so

```text
(k*b+1)*D ≤ k*q²*(q*(K0+w)+1)
             < k*w*q⁷*s² = ell < first.
```

For the strict middle inequality, `K0 < q²` reduces it to
`w*(q⁵-q) > q*K0+1`; the latter follows from
`q⁵-q³-q-1 > 0` for `q ≥ 2`. The last inequality follows from the first
norm. The new signed first residual is

```text
b*(r' - k*Bt') - Bt' = b*first,
```

so its squared residual is zero. The other two residuals remain zero by the
symmetry above. Consequently, **if a positive 89-row zero exists**, this
construction produces a positive *full 88-row zero* with `Bt' < 0`. No such
standard-natural 89-row zero is asserted to exist. In particular, this is not
an unconditional full-graph counterexample and does not disprove the
existential 88/89 equivalence. It rules out using universal `Bt > 0` as the
reverse argument in any setting admitting the assumed 89-row zero; a
different normalization or reconstruction may still work.

`check.py` pins and checks the relevant DAG dependencies, compares the entire
fixed beta and K0 payload integers, and evaluates a small first-residual
example before and after the symmetry. In that example the other residuals
are preserved but nonzero; it is not presented as a full zero. The captured
finite check passed with empty stderr. The general construction above is an
external arithmetic argument, not a Lean theorem or an internal IΣ₁ proof.
