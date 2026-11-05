# Conditional full-graph obstruction to the b-step guard

The following is an external arithmetic construction, **conditional** on
an 89-graph zero satisfying an additional divisibility property. It does not
assert that such a zero exists at the canonical fixed ports or at any other
ports, and it does not refute 88/89 existence equivalence.

Assume a positive 89-graph zero over the standard naturals, with `beta>0`,
`K0<beta²`, and additionally `b ∣ (A+1)`, where

```
b=J*beta, q=1+b, A=K0+w,
T=Bt=q*((q−F−alpha)*A−F), D=q*(q*A+1).
```

The checked 89 transport and divisibility results give `T>0` and `b∣T`;
positive witnesses give `F+alpha<q`. Algebra gives

```
D−T = q*((F+alpha)*A+F+1) > 0.
```

Because `q=1+b` and `b∣A+1`, also `b∣D`. Thus
`u=(D−T)/b` is a positive integer with `u≤D`. Replace `F` by `F+1` and
`alpha` by `alpha+b`. This preserves `G=alpha+b(q−F)` and changes the
transport to `T−D=−b*u`. The 88 main and ordinary residuals depend on these
variables through `G` and remain zero when all other relevant inputs are
kept.

Let `tau` be the old positive first Pell root, `k=eta+zeta`, and
`ell=XY²k`. The new 88 first-root witness

```
r′ = tau − (b*k+1)*u
```

is positive. To see this, `q≥2`, `w,s≥1`, `k≥2`, and
`K0<beta²<q²` give

```
(b*k+1)*u ≤ (b*k+1)*D ≤ k*q²*(q*A+1)
  < k*w*q⁷*s² = ell < tau.
```

For the strict middle inequality, `A=K0+w` and `K0<q²` reduce it to
`w*(q⁵−q)>q*K0+1`, which follows for `q≥2`. The final inequality follows
from `tau²=1+ell*(ell+k)`. Substitution gives the new first-root expression
`b*tau`, so the first residual is also zero. This constructs a positive
full 88 zero with negative transport, conditionally on the stated 89 zero.

The new `F′=F+1` still satisfies `F′<q`: the old positive transport gives
`F+alpha<q` and `alpha≥1`. The checked
[`guard_requires_large_inputs`](../ordinary12-absorb88-normalization-guard-obstruction-draft/README.md)
shows that this specific b-step normalization guard requires `F′≥q`.
Therefore this conditional full 88 zero cannot satisfy that guard. It may
still have another normalization, and the original 89 zero is already
assumed, so this is an obstruction to a proposed **universal guard proof**,
not to the existence equivalence.

## Finite illustration, not a full zero

`check.py` evaluates the pinned 88 DAG at `beta=3`, `K0=1`, `MC=MF=0`,
`J=w=s=eta=zeta=1`. It checks a one-step change from `F=alpha=1`,
`Bt=12`, `r=32797` to `F=2`, `alpha=4`, `Bt=−24`, `r=32713`, preserving
`G=10` and the first residual zero. The actual main and ordinary residuals
are unchanged **and nonzero**; neither tuple is a full zero. This finite
illustration checks the arithmetic pattern and does not establish the
conditional hypothesis above.

`python3 -I -S -B check.py` exited 0 on 2026-11-04; `result.json` preserves
its exact output. The checker raises on failed conditions even in optimized
Python. The conditional full-graph argument above is not a Lean theorem and
has not been formalized in an IΣ₁ model.

```text
graph-dag.json SHA-256 84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25
check.py SHA-256       d0f039d0707e5217d1459f7145c84ce1ad237a30cfbad6ebc1ad95ca666f5a64
result.json SHA-256    0b75c2eba58d26e2df2abe08b40e42686187302d13ffdaba965e9cc1f9db3c3a
```
