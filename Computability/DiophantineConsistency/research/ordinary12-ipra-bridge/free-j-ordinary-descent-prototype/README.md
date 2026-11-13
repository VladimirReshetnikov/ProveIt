# Ordinary-tail zero and denominator-cleared identities

The actual 95-row free-J graph's internal zero implies internal zero of its
exact polarized ordinary residual. This holds for arbitrary integer ports and
any `IΣ₁` model, with no rank or strong-norm premise.

Separately, for any commutative ring, define `w=n+V`, `p=1−Q`,
`h=pw²+QV²−1`, `b=2pw`, `A=dh+Qp`, `N=A²−dQb²`, `D=db`, and `Y=wD−A`.
Lean proves the polarization identity connecting N to the graph's polarized
shape and the denominator-cleared identity

```
QV²D² − (Q−1)Y² − D² = −(Q−1)N.
```

It also proves the latter using signed-pair semantics in `IΣ₁` models for
four **natural** model inputs. Neither this result nor the universal ring
identity is yet bound to the graph's potentially signed `V` expression. No
nonzero denominator, division, denominator cancellation, integral quotient,
positive multiplier, strong norm, or ordinary-to-compact44 checker bridge is
asserted. These are algebraic prerequisites, not the adjacent-coefficient
rational-integrality descent.

The larger experiment applying signed-pair normalization directly to four
arbitrary expressions was stopped (session 73466, exit 130) after its memory
use reached approximately 4 GiB; its source and observation are preserved
under `observations/`. It did not produce a proof. A possible modular route is
to instantiate the universal ring identity in `ModelDifferenceRing` and use
its expression-evaluation bridge, but those newer sources were not mixed into
this historical provider and require their own coherent source rebuild.
Denominator divisibility and integrality would still need proof.

Fresh historical replay session 74416 actually exited 0 and printed
`PASS_BOUNDED_FREEJ_ORDINARY_IDENTITIES
96220f794a1249fdfaadb4f2468cbd90301e572a6fced5b56d0cde1f74fa8aa5`.
The receipt records five Lean axiom reports, direct imports, hashes and the
inherited provider replay. Exploratory session 13726 also exited 0. This is a
single-author model/commutative-ring result, not a matched full-project replay,
dynamic dependency audit, or object-level iPRA proof.
