# Proposed kernel-checked formalization

**Status:** plan only. No Lean file in this package has been compiled; no theorem
has been added to ProveIt's formal proof ledger.

## 1. Exact arithmetic and finite Laurent polynomials

Represent Z[zeta] by pairs of integers with the multiplication and conjugation
formulas in `CERTIFICATE.md`. Prove an embedding into the complex numbers that
sends `(0,1)` to `exp(2*pi*i/3)`. Define finite Laurent polynomials by finitely
supported maps from integer exponent vectors to this coefficient ring.

Prove that coefficient equality implies equality after evaluation on unit
complex variables, and formalize the conjugate-transpose Gram expansion with
exponent `v-u`. This is a reusable infrastructure milestone.

## 2. The two finite polynomial identities

Enumerate F_3^2, its 4-direction cubes, and all 16 vertices. Reconstruct the
original twisted cube polynomial. Independently construct the twelve-line
formula and substitute its integer exponent map. Check coefficient equality
using kernel-reduced finite computations or a verified reflection procedure.

Reconstruct the 241-element basis and verify the Gram coefficient identity from
the stored integer matrices. Importing a Boolean result from the Python checker
as an axiom would not constitute this milestone.

## 3. Positivity without numerical spectral theory

Prove the elementary Hermitian diagonal-bound lemma using
`2 |x_i x_j| <= |x_i|^2+|x_j|^2`. Check all rational bounds for the supplied
triangular factor. Prove the abstract implication

```text
Q Hermitian, QK=0, Q+K K* positive definite
    => Q positive semidefinite, kernel(Q)=range(K).
```

Verify rank 28 using a modular minor or a kernel-checked elimination trace.
This also yields the feature-space stability theorem.

## 4. Equality and the phase quotient

Formalize the four family substitutions and the support of the separator
polynomials. Verify all 81 constant-class values. Prove the line-incidence
identity and the torus-map degree statement. Establish the explicit cubic
kernel and the base-phase formulas. The component count requires elementary
facts about closed subgroups and finite coverings of tori; it can be postponed
without postponing the sharp energy bound or the explicit parametrization.

## 5. Analytic extension and all dimensions

Use an established finite-group Gowers U^4 norm and its mixed Cauchy--Schwarz
inequality. Prove the Z/9 x Z/3 cover primitive, gauge identity, convexity and
strict-convexity argument. Then prove the general characteristic-three
integration criterion and lossless subgroup comparison, and restrict a
nonzero alternating defect to a plane.

The exact theorem endpoint is: for an already symmetric four-linear tensor T,
energy above 11/27 implies existence of a nonclassical quartic primitive.
Approximate symmetrization is not silently included.

## Integration discipline

Keep research statements separate from compiled facts. Record precisely which
milestones have been kernel checked before updating any status ledger. Preserve
the attribution of the general integration criterion and finite-cover method.
Do not create placeholders with `sorry` and describe them as formalized results.
