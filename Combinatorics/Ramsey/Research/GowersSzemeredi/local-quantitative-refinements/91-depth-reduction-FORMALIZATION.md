# Formalization plan: sharp critical-depth reduction

This is a plan, not a report of completed Lean verification. No Lean source or
placeholder axiom is included. The human proofs are in `article.tex`.

## 1. Separate namespace and interface

Use a separate namespace beneath the research development; names below are
proposals, not assertions about existing Mathlib declarations. The inspected
repository interface is

    Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections17_18.lean

at commit `b9760ed931282087ee57cb1ffb66dc66e40ee47b`, blob
`18495f50475835ca1c497d85b0052215f865b8ca`.

The existing Proposition 17.2 uses a cyclic prime field, a factorial-unit
hypothesis, a multiaffine selector, and an energy conclusion. The proposed
results use vector spaces over a prime field, circle-valued additive
polynomials, and correlation inputs. They are not drop-in replacement proofs.

Do not conflate a general additive polynomial with a coordinate polynomial
unless the value group and degree equivalence have been established. In
particular, replacing the circle by F_p destroys the genuinely nonclassical
phases.

## 2. Objects to define

| Proposed object | Mathematical specification |
|---|---|
| `AdditivePolynomialDegreeLE` | Every (d+1)-fold additive difference vanishes. |
| `PhaseDepthLE` | P-P(0) has values in p^(-(a+1)) Z/Z. |
| `normalizedCorrelation` | Uniform or explicitly weighted average of f times conjugate(g). |
| `digitLift` | The standard representative of t in {0,...,p-1}, divided by p^(a+1), in the circle. |
| `stepCorrection` | Indicator of the representative inequality t<j, divided by p^a. |
| `criticalDepth` | d_a = 1+a(p-1), with a>=1. |
| `candidatePhase` | Q-stepCorrection(L). |
| `correlationEnvelope` | Maximum absolute correlation over the finite normalized phase family. |

Model the circle additively, or work in explicitly embedded finite cyclic value
groups after normalization. Constants must be quotiented out or carried through
as scalar rotations. A depth-a phase is represented modulo p^(a+1); its reduced
candidate is represented modulo p^a, not in the same finite target by accident.

The complex inner product is linear in its first argument throughout the paper.
Signs and conjugations must be translated if a library convention differs.

## 3. Algebraic milestone

The main dependency sequence is:

    translation operators
      -> (T_h-1)^p = -p (T_h-1) U(T_h-1)
      -> finite inverse for U on polynomial functions
      -> multiplication-by-p lowers degree by p-1
      -> cyclic finite-value degree bound
      -> exact digit degree and step degree bound
      -> critical top residue is linear
      -> Q and every candidate have the required degree and depth

The polynomial U has integer coefficients and constant term one. Its inverse
on the relevant nilpotent module is a finite integer polynomial. There is no
division by p in the target circle in this argument.

A crucial proof obligation is mixed derivatives: it is not enough to check
repeated derivatives in one direction. The inverse operator commutes with all
translations, and every mixed derivative of a polynomial is still controlled.

For the cyclic finite-value bound, prove

    D^(1+b(p-1)) = (-p)^b D U(D)^b

and use that p^b annihilates the values. Then every directional difference on
F_p is divisible by D=T_1-1. Composition with a linear map preserves degree.

The normal form follows from p^a P having degree at most one after P(0)=0.
Its image is in the p-torsion of the circle, giving a unique F_p-linear L.
Prove both implications of L != 0 iff exact depth a.

## 4. First analytic milestone: transfer without sharpness

Fix m=p^a, zeta=e(1/(pm)), omega=zeta^p. The exact finite identity is

    sum_j zeta^j omega^(-1_{t<j})
      = sum_{r=t-p+1}^t zeta^r
      = p d_0 zeta^t.

This should be proved by reindexing two finite sums. It is the easiest
substantial theorem to kernel-check: no inverse theorem, spectral theory, or
optimization is needed.

Then prove |d_0|=c_{p,a}>0 by a geometric sum, derive the pointwise phase
identity, and integrate it against arbitrary probability weights. The triangle
inequality gives the scalar transfer. Cauchy–Schwarz and finite averaging give
the common-index aggregate-energy theorem.

Keep the pointwise equality as an exported lemma: it is stronger and easier to
reuse than a single existence theorem on uniform measure.

## 5. Sharpness and equality classification

These require a distinct geometric lemma: among p distinct vertices of a
regular pm-gon, the maximum resultant length is attained exactly by a block of
p consecutive vertices. A possible formal route is projection onto the sum
argument and selection of the p largest projections.

The equality proof must handle ties correctly. At the maximizing block's
midpoint direction there is a strict gap between selected and excluded
vertices. A numerical enumeration of roots cannot replace this proof.

For the unrestricted lower-depth competitors, condition on the nonzero linear
form L. Its fibres have equal cardinality. Their conditional values lie in the
convex hull of mth roots. Equality in the convex combination forces a single
maximizing root pattern because different maximizing blocks have different
sum arguments. Equality in the average of unit vectors then forces agreement
on each fibre. The article's p step phases, modulo constants, are all cases.

Separate declarations for the inequality, its sharpness example, and its full
equality characterization are preferable.

## 6. Arithmetic list minimality

Prove the cyclotomic extension degree

    [Q(zeta_{p^(a+1)}):Q(zeta_{p^a})] = p.

The article gives an Eisenstein proof of the prime-power cyclotomic degrees.
Then the p entries 1,zeta,...,zeta^(p-1) are linearly independent over the smaller
field. A K-valued matrix with fewer than p columns has a nontrivial left null
vector. Conjugating this vector produces a test function annihilating every
candidate correlation but not the target correlation.

The quantifier order is essential: candidates may depend on P but must be
fixed before f. This is not a lower bound against an adaptive algorithm
outputting one selected phase. Arbitrary constant rotations of candidates do
not change the span argument.

## 7. Frame and stability milestone

Use the p-dimensional complex inner-product space with normalized counting
measure. Define the twisted cyclic shift and diagonalize it in the orthonormal
basis v_r(t)=zeta^t e(rt/p). The atom vectors are the orbit of the constant-one
vector. This yields

    zeta^(-j) s_j = sum_r beta_r conjugate(d_r) e(rj/p).

Finite Parseval proves the score-energy identity. Nonvanishing of d_r gives
invertibility of the score map and the conditional stability estimate.

The article proves the optimal square-root *exponent*, not the best stability
coefficient. Do not export a claim that the displayed singular-value bound is
an optimal nonlinear coefficient.

In the full vector space the controlled object is the conditional twisted
function F(t)=E[f e(-Q) | L=t]. The orthogonal fibre component of f is invisible
to these scores; the theorem does not prove closeness of f itself to a phase.

## 8. Computational status and acceptance criteria

`code/verify.py` tests exact integer exponent identities and finite modular
examples; its root optimization and spectral diagnostics use double precision.
Neither the generated JSON nor the Python assertions are trusted Lean proofs.

A useful first completed module would prove the degree budget plus the exact
pointwise identity and weighted transfer. Mark sharpness, list minimality, and
stability separately until their own proofs compile. Before any formal ledger
update, check exported theorem types, use no `sorry` or new axiom, and record
the actual toolchain, imports, and kernel-check result.
