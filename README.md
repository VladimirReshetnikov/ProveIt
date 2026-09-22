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
The numeric-game field and game-graph recursion reuse a pinned subset of
[combinatorial-games](vendor/combinatorial-games/README.md), with three
documented proof-script adjustments for this Lean version. Its source and
Apache license are included in the repository.

## Formalization

The [source documents](docs/README.md) comprise eighteen research reports and
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
It extends to Mathlib's projective line, with the homogeneous direction
product law and an explicit treatment of the point at infinity.
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
Viète's formula and both Newton recurrences use finite root multisets.
Resultants have their Sylvester determinant and root-product formulas,
with common-root and finite Bézout-kernel criteria.
The native discriminant has its signed-resultant and squared-root-difference
formulas, with squarefree and repeated-root criteria. Strict upper and lower
Cauchy bounds and the radial coefficient bound use the base-field modulus,
including non-Archimedean scales and zero-radius cases.
Gauss–Lucas uses positive convex weights in that same ordered base field;
its barycentric formula retains root multiplicities. Higher-derivative
inclusion keeps the required intermediate splitting hypotheses explicit.
For monic quotients over any commutative coefficient ring, finite remainder
coordinates give multiplication matrices, trace and norm. The top-remainder
coefficient defines a perfect residue pairing with an explicit dual basis,
and multiplication trace equals the residue of the derivative times the class.
These identities also hold with zero divisors, repeated roots and positive
characteristic.
The residue Gram determinant is the fixed reversal sign and its inverse is
the coefficient matrix of the finite bivariate Bézout kernel. The trace Gram
matrix factors as the residue Gram matrix times multiplication by the derivative.
The quotient norm equals the polynomial resultant over every commutative
ring, so the trace Gram determinant equals the native discriminant even
in positive characteristic. A verified formal Laurent inverse also identifies
the residue functional with the coefficient at infinity.

The Hahn layer uses mathlib's `SummableFamily` and proves the full Neumann
support lemma, including finiteness across all word lengths. It distinguishes
Hahn summation from ordinary summation of constant coefficients and exposes
univariate evaluation only with a positive-order proof. Geometric-series
identities and exact finite remainders are formal Hahn identities.
Evaluation commutes with univariate formal composition when the inner series
has zero constant coefficient.
Admissible binomial expansions satisfy exponent addition and give the unique
natural-degree root near one over a characteristic-zero coefficient field.
Over ordered coefficients, the half-power is the unique nonnegative square
root of a positive-order perturbation of one.
Arbitrary regrouping and double-sum interchange preserve jointly summable
families. Coefficient-zero extraction gives standard part on the nonnegative-order
subring, with residue field and a unique constant-plus-infinitesimal decomposition.
Roots of monic polynomials over this subring stay in it; for split polynomials,
standard part preserves the root multiset with multiplicities.
Resultant and nodal-derivative valuations are finite sums of root-separation
valuations, with infinity retained when a product vanishes.
Discriminant valuations give twice the pairwise separation sum with the
leading-coefficient term; in the monic case they also equal the sum of
derivative valuations at the roots.
The weighted Gauss valuation is the finite minimum of weighted Taylor
coefficient valuations at any center and scale. Its initial polynomial is
nonzero for nonzero input, is multiplicative, and equals coefficientwise
standard part after monomial normalization.
Its support consists exactly of the active indices attaining the weighted
minimum, with degree and trailing degree giving their extrema.
For explicitly split polynomials, the initial factorization counts roots in
closed balls, open balls, shells and individual residue directions, preserving
multiplicities even when their residues coincide.
The resulting Newton profile counts roots at each finite valuation and identifies
its finite set of breakpoints. Perturbations of strictly higher weighted
valuation preserve the entire initial polynomial and these local root counts,
even when the polynomial degree changes. In residue characteristic zero,
differentiating through the initial polynomial's degree lowers the weighted
value by the expected multiple of the scale and differentiates the initial
polynomial exactly. Occupied open and closed valuation balls consequently
contain exactly `k-r` roots of the `r`th derivative in the permitted range,
with explicit splitting assumptions and multiplicities retained.
For squarefree split polynomials of degree at least two whose derivatives
split, each root has a critical point at exactly its nearest-neighbour
valuation, and no critical point is closer in valuation.
Coefficientwise real and imaginary parts identify Hahn series over `R[i]`
with the quadratic extension of Hahn series over `R`. This identification
also uses Mathlib's native real and complex coefficients; conjugation fixes
exactly the embedded real Hahn series and preserves support and valuation.

The independent foundational track now constructs ordinal-length sign
sequences with the numerical first-disagreement order, well-founded prefix
simplicity and an ordinal order embedding. Birthday-bounded fragments are
small, while the full carrier is not small at the same universe level.
Every small separated cut now has a canonical simplest separator with a proved
birthday bound. The cut operation reconstructs canonical sign options, respects
reindexing and satisfies Conway's negation rule. It gives upper, lower and
positive lower bounds for small families. Small sets with no greatest member
have no supremum; embedded finite ordinals give a concrete bounded example.
Conway addition is now constructed by well-founded recursion with proved
option separation. Its zero, commutativity, associativity, inverse and order
laws make the sign carrier an ordered additive commutative group. The addition
cut equation also holds for arbitrary small presentations of the summands.
Native natural-number casts agree with finite all-plus sequences, and integer
casts form an additive order embedding. Subtracting one from any upper bound
of the naturals proves directly that they have no supremum.
The ordered field extends these casts to rationals and ordinary reals.
Halving any upper bound of the naturals gives another strictly smaller upper
bound. The all-plus sequence of length omega exceeds every embedded real;
its reciprocal is positive and smaller than every positive embedded real.
Ordinal signs use Hessenberg natural addition and multiplication, with an
explicit counterexample to preservation of ordinary ordinal addition.
In its native order topology and compatible additive uniformity, every small
subset is closed and discrete, convergent small-index nets are eventually
equal to their limits, and small-index Cauchy nets are eventually constant.
The whole carrier has no isolated points. Neighborhoods and entourages use
absolute differences valued in the sign carrier itself.
The net of all positive radii, directed by reverse order, converges to zero
and is Cauchy but is never eventually constant. Its index type is proved
not small at the lower universe level.
Canonical sign options also define a small, well-founded game graph. Its
recursive game construction preserves and reflects comparison, proves the
image games numeric, and gives an explicit order isomorphism with the reused
numeric-game surreal field. Every small cut is preserved, and induction on
numeric-game options proves surjectivity. The bridge preserves the original
Conway addition, sign reversal, zero and one. Transporting the proved game
multiplication and inverse then makes the sign carrier an ordered field,
retaining its original additive structure and numerical order.
This product satisfies Conway's four-family simplest-cut equation, with
small option indices and proved separation.
The equation also holds for arbitrary small presentations of both factors.
The empty and one-plus sequences map literally to the raw games zero and one.
The numeric-game quotient also satisfies the indexed small-cut interface and
its comparison rule, including reconstruction from a numeric game's moves.
The canonical raw-game birthday equals sign length and is minimal among
all numeric games representing the same number.
The birthday of a sum is bounded by the Hessenberg natural sum of the input
birthdays, with the corresponding finite-sum bound. This natural sum also
strictly decreases under either canonical option replacement.
Finite birthdays characterize exactly the embedded dyadic rationals. They form
a subring, but the reciprocal of three has birthday omega, so this fragment
is not a subfield. Every embedded ordinary real has birthday at most omega;
the non-dyadic reals have birthday exactly omega.
The concrete surcomplex field is now the quadratic extension of that sign
field. It has the coordinate product, conjugation and inverse formulas, a
positive surreal-valued norm square away from zero, and dimension two over
its real subfield. Its carrier is also not small at the birthday universe.
Its native topology and uniformity are the product of those on the two surreal
coordinates. Balls defined by `normSq (z - a) < r²`, for positive surreal `r`,
give the neighborhood and entourage bases without requiring square roots.
Small subsets are closed and discrete; convergent small-index nets are
eventually equal to their limits, and small-index Cauchy nets are eventually
constant. The full surcomplex carrier has no isolated points.
Multiplication is jointly continuous, inversion is continuous away from zero,
and conjugation is a uniform equivalence. The real-axis positive-radius net
converges to zero and is Cauchy without becoming constant; both its index
type and range are proved not small at the permitted universe level.
The surreal field is not algebraically closed, and no linear order is
compatible with surcomplex multiplication.
Real closedness and the normal-form bridge to Hahn series remain open.
A successful build proves only the imported Lean
statements, not coverage of all the source documents.
