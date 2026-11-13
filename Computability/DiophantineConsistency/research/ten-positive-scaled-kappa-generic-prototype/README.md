# Positive scaled projection quotient without graph zero

`TenPositiveScaledKappaGeneric.positive_kappa` assumes in an IΣ₁ model only
`X=2^R` and `X<ycoord(R,a)`. With `C=ycoord(R,a)` it constructs positive κ
satisfying

    X*(3*C-2*X)+2 = (4*a+3)*κ.

The natural subtraction is justified by the supplied size bound. The proof
uses the generic Pell projection and norm, the factored unweighted projection
identity, and the existing signed-to-natural divisibility transfer. There is
no graph-zero assumption and no cancellation by a graph factor. This is a
conditional reverse-carrier ingredient, not yet the 80 carrier construction,
a graph implication, external coefficient binding, or an iPRA proof.

Accepted guarded check `observations/kappa-attempt02/` produced
`/tmp/scaled-kappa-generic-lhzfzgtx/ScaledKappaGeneric.olean`, SHA-256
`947e0b19ed344707c91897947e6b75f2e62ca61fadbaf968e1c3d0656b5d8007`.
Attempt01 failed to unfold a natural-to-difference-ring cast and had an
unused-simp warning. All three source-direct imports are preflighted against
selected paths and hashes before and after Lean. Broader transitive
source-object, project/package and dynamic-library limits remain inherited.
