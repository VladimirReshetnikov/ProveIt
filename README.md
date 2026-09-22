# Surreal

Lean formalization of the theorems about surreal and surcomplex numbers in
the project's source documents, following their proposed formalization plan
and beginning with the simplest prerequisites.

## Build

The project pins Lean and mathlib to version `4.32.0`; `lake-manifest.json`
records the exact dependency commits. With [elan](https://github.com/leanprover/elan)
installed, run:

```sh
lake exe cache get
lake build
```

Lean warnings are treated as errors, including warnings for incomplete proofs.
The default build also checks `SurrealAudit.lean`, which rejects transitive
axiom dependencies other than `propext`, `Quot.sound`, and `Classical.choice`.

## Formalization

The [source documents](docs/README.md) comprise fifteen research reports and
their preserved source manuscripts. The
[coverage and dependency ledger](docs/FORMALIZATION.md) records their statements,
the proposed Layer A–E implementation order, and the exact scope of each
implemented result.

The first modules establish size obstructions and reusable finite algebra.
Complexification uses mathlib's `QuadraticAlgebra`, with its cross-term
multiplication, conjugation, and field construction. The modulus takes values
in the ordered base field. Polynomial results reuse mathlib's splitting,
algebraic-closedness, and integrality theorems.
The rational circle chart is an equivalence from the ordered base field to
the norm-square-one points other than `-1`, with inverse `im / (1 + re)`.
Finite geometry includes Heron's area identity, Ptolemy's inequality and the
positive-quotient criterion for equality in the triangle inequality. Formal
polynomial derivatives give multiplicity, finite Taylor expansion and the
divisibility criterion for equal jets.
Polynomial algebra also includes unique division and factorization, monic
Bézout gcds, principal ideals, and the exact gcd-with-derivative formula.
Finite Hermite interpolation realizes prescribed derivative jets at distinct
nodes by a unique polynomial below the total multiplicity degree bound.
The polynomial CRT identifies the quotient with the product of local jet
rings and provides orthogonal idempotents summing to one. Explicit truncated
inverse jets construct their polynomial representatives, with coefficients
computed by repeated formal differentiation of the reciprocal. The simple-root
case gives the Lagrange formula, with nonzero derivative denominators.
The finite inverse-jet weighted sum gives an explicit Hermite interpolant
after taking its polynomial remainder.

The Hahn layer uses mathlib's `SummableFamily` and proves the full Neumann
support lemma, including finiteness across all word lengths. It distinguishes
Hahn summation from ordinary summation of constant coefficients and exposes
univariate evaluation only with a positive-order proof. Geometric-series
identities and exact finite remainders are formal Hahn identities.
Arbitrary regrouping and double-sum interchange preserve jointly summable
families. Coefficient-zero extraction gives standard part on the nonnegative-order
subring, with residue field and a unique constant-plus-infinitesimal decomposition.
Roots of monic polynomials over this subring stay in it; for split polynomials,
standard part preserves the root multiset with multiplicities.
Coefficientwise real and imaginary parts identify Hahn series over `R[i]`
with the quadratic extension of Hahn series over `R`. This identification
also uses Mathlib's native real and complex coefficients; conjugation fixes
exactly the embedded real Hahn series and preserves support and valuation.

These generic prerequisites do not yet construct the surreal field or establish
the normal-form bridge to Hahn series. A successful build proves only the
imported Lean statements, not coverage of all the source documents.
