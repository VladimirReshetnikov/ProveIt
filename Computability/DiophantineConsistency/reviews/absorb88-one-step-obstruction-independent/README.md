# Independent review of the conditional one-step obstruction

The [external conditional argument](../../research/ordinary12-absorb88-one-step-conditional-obstruction/README.md)
is consistent with the stated arithmetic assumptions. It is not a Lean
proof and it does not establish the existence of the required full 89
zero. This review did not invoke Lean or independently replay the
imported 89 transport/divisibility and 88 guard-necessity theorems.

Assuming the stated positive standard-natural 89 zero and `b ∣ A+1`,
the cited positive transport and `b ∣ T` give `0<T<D` and `b ∣ D`.
Indeed `q≡1 (mod b)`, so `D=q(qA+1)≡A+1≡0 (mod b)`. Hence
`u=(D−T)/b` is a positive integer with `u≤D`. The update
`F′=F+1`, `alpha′=alpha+b` preserves `G=alpha+b(q−F)` and sends
the scaled transport from `T` to `T−D=−b*u`. The graph sources show that
the main and ordinary residuals use `F,alpha` through this unchanged
`G`, and do not use the replaced first-root coordinate.

For the first coordinate, the estimate in the packet is valid under its
positivity and `K0<beta²` assumptions. Here `q≥2`, `k≥2`, `w,s≥1`,
and `K0<q²`; using `(b*k+1)≤q*k` and `u≤D` reduces the desired bound to
`w(q⁵−q)>q*K0+1`. Since `w≥1`, `q≥2` and `K0<q²`, the left side exceeds
the right side. The Pell norm gives `tau>ell`, so the proposed
`r′=tau−(b*k+1)u` is positive. Direct substitution in the 88 first-part
expression yields `b*tau`, and the first residual vanishes. Together
with preservation of the other two residuals, this is the stated
conditional full-graph construction.

The same original positive transport gives `F+alpha<q`, and `alpha≥1`
gives `F′=F+1<q`. The cited necessary condition for the particular
normalization guard requires `F′≥q`, so that guard fails for the
conditionally constructed 88 zero. This says nothing about a different
normalization, does not refute existence equivalence, and does not show
that the conditional full-zero hypothesis holds for the fixed ports.

The finite Python illustration was rerun read-only and reproduced its
recorded JSON byte-for-byte; both main and ordinary residuals are
explicitly nonzero. The digest and illustration check is:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/absorb88-one-step-obstruction-independent/review.py
```

The captured output is [`result.json`](result.json). Hashes:

```text
e8321cfbad7124082ece4337039e45192ebde04be2e84bc8ecdcb6e56ad8c561  review.py
2aafa6d80f66270847638a46500e743009e9238ffca8eadac622b2cd819deb64  result.json
```
