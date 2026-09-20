# Mathematical and verification status

Date: 20 September 2026.

## Selected target

The unnumbered experimental identity in Section 9.5, “Multiple chains,” of
Athanasiadis–Chapoton, arXiv:2605.26916v1, for the chain preorder tau_(n,d)
with n equivalence classes of size d. The source uses t^2 and a Laurent
normalization; Section 1 of the article explicitly converts it to an identity
in Q[t][[z]]. This target is different from the reciprocity/duality and
root-polytope realization claims recorded in the uploaded manifest.

## Provenance of this package

This is a merge of two independently prepared packages that proved the same
identity by different routes:
`enumerative-combinatorics/multiple-chain-exponential-formula` (the base;
two-subset encoding, excursions, constant term, rectangular generality) and
`enumerative-combinatorics/multiple-chains-exponential-identity` (slack
meanders, positive-part factorization in Q[t]((u^-1))[[z]], stars and bars,
diagonal case only, plus fixed-support and mixed-size theorems). Section 1.2
of the article records this, and Section 1.5 lists every result deliberately
retained in two versions.

## What the article establishes

Theorem 2.1 proves the rectangular exponential formula for every d>=1 and
c>=0, by the subset-encoding/excursion argument. Section 3 proves the same
theorem again by the original-coordinate slack process. Taking c=d proves the
selected multiple-chain identity for every block size. No case of that identity
is left over. Neither proof assumes the correctness of any research package
catalogued in the supplied manifest. The main formal proofs are independent of
both the analytic consequences and the computer calculations.

The article additionally proves:

* a support-preserving d/c duality and exact convolution/partition formulas,
  including the weighted permutation average and the symbolic rows H[2,d],
  H[3,d], H[4,d];
* the endpoint-refined factorization, recording the joint distribution of
  support and unused budget;
* uniform-dilation Ehrhart evaluation formulas;
* a finite radical product and algebraic degree upper bound 2^d, proved twice
  (conjugate counting and an explicit monic polynomial of degree 2^d);
* the explicit double-chain quartic, with its formal branch uniquely specified
  and two independent elimination certificates;
* a block-boundary gamma interpretation and an algebraic constant-term
  derivation of the same gamma generating function, together with integrality,
  strict positivity in every permitted degree, and strict increase to the
  centre (the qualitative gamma-positivity itself was already known);
* for each fixed support size j>=1, polynomial dependence on n of exact degree
  2j with leading coefficient d^(2j)/(j!(j+1)!), plus the explicit first two
  support coefficients;
* a Stieltjes moment representation in the number of blocks and strict Hankel
  determinant positivity for real t>0;
* a commutative mixed-block-size formula summed over orders, together with an
  explicit counterexample showing that the support polynomial is not a
  function of the multiset of block sizes;
* fixed-d, positive-t n^(-3/2) asymptotics with an explicit leading constant,
  given both as a finite radical product and as a convergent exponential sum;
* the exact support mean and variance, a central limit theorem, and the
  constant-order variance correction kappa_d.

## Prior results and nonclaims

The two-subset encoding is closely related to the one in Athanasiadis,
arXiv:2510.23903v1. Gamma positivity for all composition polytopes was already
proved in that paper. The excursion/meander factorization is classical
Spitzer/Wiener–Hopf theory; its short formal proof is supplied rather than
claiming the factorization itself as new. Square-root singularity transfer is
established analytic-combinatorics machinery, with its hypotheses checked in
place.

The following are explicitly **not** claimed:

* no independent refereeing and no proof-assistant certification;
* no exhaustive proof of novelty or priority; the target remains experimental
  in the retrieved v1 source, and targeted searches found no later proof, but
  absence from those search results is not evidence of absence;
* no new general Wiener–Hopf/Spitzer factorization theorem;
* no new resolution of qualitative gamma-positivity for composition polytopes;
* no solution of real-rootedness, gamma positivity for arbitrary preorders,
  flag realizability, or the general weighted q-reciprocity conjecture;
* no claim that the degree bound 2^d is sharp, or that any particular minimal
  algebraic degree holds;
* no order-invariance for unequal block sizes; an explicit counterexample is
  given, and no closed formula for a single prescribed order is claimed;
* no claim that the support polynomial is the Ehrhart h*-polynomial of
  Q_(n,d), or that the Ehrhart evaluation proves real-rootedness;
* no uniform asymptotics for d growing with n or for t approaching zero, and
  the asymptotic statement excludes t=0;
* no claim of novelty for every displayed corollary independently.

## Verification actually performed

See `results/verification.json` for exact counts and ranges of both suites.
Suite 1: three exact methods agree on all 315 rectangular triples; 34,689
feasible arrays were also visited exhaustively; gamma path enumeration and
exact rational variance checks use separate algorithms. Suite 2: a block-weight
slack dynamic program agrees with the recurrence on all 104 diagonal
polynomials for 1<=d<=8, 0<=n<=12, with independent coordinate enumeration,
endpoint-factorization, fixed-support finite-difference and mixed-size checks.
Neither range was narrowed in the merge. The quartic was derived by two
symbolic resultants and independently checked as a truncated polynomial
identity coefficientwise in t.

The article was compiled with `latexmk -pdf`. The build log contains no
overfull or underfull box warnings, no unresolved references, and no undefined
citations; `results/pdf_validation.json` records this. No page-image
inspection is claimed for this merged build.

This is an AI-assisted, unrefereed research draft. It has not been checked in
a proof assistant or independently reviewed by a mathematician. Exact finite
computations are consistency checks, not replacements for the written proofs.
Numerical asymptotics use 80-digit working precision, not certified intervals.
