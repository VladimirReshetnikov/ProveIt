# Proof audit and verification boundary

This is a proof-dependency and self-review record, not an independent referee
report or a machine formalization.

## Central theorems

**Theorem 5.1 — whole-relative-infinitesimal normalization.**
The exact equations reduce to `h = H f - Pi (exp(h)-1-h)`. Homogeneous recursion
constructs a unique formal solution. Its coefficients are polynomials in the
finitely many integral entries of Pi, not arbitrary elements of the valuation
ring. Lemma 3.4 (finite-generator evaluation) supplies strong summability at every
infinitesimal input. Uniqueness is a single strict-valuation contradiction and
requires no convergence of repeated iterations.

**Theorem 6.2 — sharp nonlinear tree-gap law.**
For two solutions, reweight by `p * exp(k) * phi(h-k)`. These new weights have
exactly the original positive leading data. The nonlinear difference becomes
an exact weighted projection. The row expansion uses precisely the trees that
avoid the target edge. A one-coordinate input makes all their cycle functionals
equal to the same scalar, so the numerator cannot have leading cancellation.
This proves equality and the leading coefficient, not merely a generic bound.

**Theorem 6.4 — all Taylor coefficient bounds.**
The formal tree denominator divided by its constant value is an integral formal
unit. Each target-row numerator term contains a scalar with valuation at least
the deletion gap. This proves bounds at every order. The strong evaluation was
already established separately; formal inversion by itself is not used as an
analytic convergence argument.

**Theorem 8.1 — nonlinear chain propagation.**
Conservation puts the actual output change in the square-cycle basis. The exact
secant matrix is tridiagonal. Although it depends on the unknown nonlinear
solution, its leading data do not. Strict dominance in the continuant recurrence
and an exact cofactor formula therefore give valuations of the actual solution,
not only its derivative at zero.

**Theorem 10.1 — real-linear-constraint extension.**
Cauchy–Binet sums over column bases with positive real determinant-square factors.
Basis interpolation matrices have constant real entries. This is why the same
integrality and support argument works. The constraint matrix is explicitly real
and constant, not an arbitrary Hahn-valued matrix.

## Delicate points checked

1. Integrality of arbitrary formal coefficients is insufficient at higher rank.
   Example 3.5 gives an explicit failure. The proof uses a common finite-generator
   coefficient algebra to avoid this issue.
2. Strong summability is not convergence of finite Taylor sums. Both the theorem
   and the remainder certificate keep this distinction explicit.
3. A surcomplex field is not ordered. “Positive-leading” refers only to the
   leading coefficient and is used to rule out cancellation in finite sums.
4. The secant weights preserve both valuations and leading coefficients, including
   for complex perturbations. No false assertion of real positivity of those
   entire weights is made.
5. Infinite gain means an exactly fixed bridge entry. Empty tree minima are
   explicitly assigned positive infinity.
6. The sharp costs are those of the normalized base matrix, not automatically
   those of an arbitrary unnormalized kernel.
7. All stability claims keep the margins fixed. A tree example shows failure when
   even relatively infinitesimal margin changes are permitted.
8. Local normalization requires no divisibility. Global positive existence is
   separated and uses real closedness; a 2x2 example shows global ramification.
9. Surreal statements are obtained by finite-data, set-sized support-group
   localization. No class-sized sums, nets, or compactness are invoked.
10. The phase-cancellation examples demonstrate actual loss of integrality and
    nonuniqueness when the positivity hypothesis is removed.

## Imported inputs

Hahn-field arithmetic and Conway normal form; Higman's word theorem; finite
linear algebra (Cauchy–Binet, Cramer's rule, incidence minors); classical real
matrix scaling and real-closed-field transfer for the global interpretation.
Each is credited. The local proof does not depend on a global surcomplex
exponential, a surreal derivation, spherical completeness, or Banach contraction.

## Computational status

`code/verify.py` and `data/verification.json` record exact finite and finite-order
checks. They do not prove the arbitrary-rank support theorem. No Lean proof is
included. The theorem labels and proofs in the article, rather than test counts,
are the mathematical deliverable. See SOURCE_AUDIT.md for the separate, limited
priority assessment.
