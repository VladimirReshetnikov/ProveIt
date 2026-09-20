# Status and proof audit

Date: 20 September 2026.

## What is claimed

This package contains a complete mathematical proof draft of **Conjecture 8
of arXiv:2111.14492v3**, for all k >= 1 and n >= 0, rather than a proof only
for a finite range or only of positivity.

The central determinant identity is proved also for k=0. The normalized
answer is the rectangular Schur specialization s_(n^k)(1^k,t^k).
The asserted consequences cover polynomiality, positive full coefficient
support, degree kn, palindromicity, weak unimodality, the rational numerator
formula, exact numerator degrees 2j(k-j), and the specified reciprocity.

## Logical dependencies

1. The binomial moment definition gives the constant-term identities directly.
2. The linear map Phi is not an algebra homomorphism. Four parity cases
   establish the Gram entries; multiplicativity of Phi is never assumed.
3. A triangular Laurent basis change and explicit parity-dependent exponent
   sums give precisely t^floor(n^2/4).
4. Dual Jacobi–Trudi identifies the resulting Toeplitz determinant.
5. A tableau complement bijection gives the positive partition sum.
6. The Schur-module character theorem plus finite-dimensional SL(2) weight
   strings proves unimodality.
7. A fully specified confluent alternant, Laplace signs, and complementary
   column subsets prove the remaining numerator assertions.
8. The recurrence and asymptotic theorems follow from these explicit formulas.

The imported classical facts are the Jacobi–Trudi, dual Jacobi–Trudi,
Schur alternant/tableau identities and the Schur-module character theorem.
They are identified and cited in the article. The needed SL(2) weight-string
argument and the binomial-Vandermonde calculation are explained in the proof.
No conjectural or unverified result from the input manifest is imported.

## Degenerate cases

- The empty determinant is 1.
- k=0 gives the unshifted determinant directly.
- n=0 gives the empty Schur polynomial and the full numerator identity.
- t=0 is reached through the proved polynomial identity, not by dividing
  specialized determinant values.
- t=1 is evaluated by an explicit dimension product, not a singular rational
  expression.
- The recurrence is minimal over Q(t) for indeterminate t. Its minimal order
  need not remain the same after specialization.
- Asymptotics are for fixed k and fixed t in the indicated regimes, not
  uniform in t approaching 1.

## Computational verification actually performed

Primary exact grid: k=0,...,6; n=0,...,10.

- 77 parameter pairs.
- 231 comparisons of three determinant formulas with the positive partition sum.
- 66 reconstructions using the explicit numerator blocks.
- 35 independent Leibniz signed-permutation determinant audits.
- Coefficient support, symmetry, unimodality, dimension, stable edge,
  coefficientwise monotonicity, block degree and reciprocity checks.
- Zero disagreements.

Supplementary exact checks:

- 66 checks of the first coefficient beyond the stable edge.
- Six leading-coefficient checks for the asymptotic deficit, using exact
  finite differences in n rather than numerical fitting.
- Nine recurrence windows for k=1,2,3, using raw Hankel determinants up to
  order 14.
- Zero disagreements.

Both verifiers use only Python's standard library and integer arithmetic.
Shared arithmetic code means this is not independent external verification.
The finite checks do not prove the unbounded statements; the article does.

## What is not claimed

- No independent referee approval or proof-assistant formalization.
- No guarantee of bibliographic priority.
- No resolution of odd-shift Conjecture 9.
- No resolution of the separate numerator-degree and reciprocity parts of
  Conjecture 10 (the denominator is obtained as an additional consequence).
- No new resolution of Conjectures 13–15, already listed in the manifest.
- No generic strict unimodality, real-rootedness, or log-concavity theorem.
- No claim that Cigler's already displayed small-shift examples are new.

## Open-status assessment

The primary source explicitly labels the selected assertions Conjecture 8.
Its arXiv record still presented v3, dated 30 December 2021, at the time of
this research. Targeted public searches did not reveal an earlier resolution.
A search can miss unpublished work, different terminology, or a resolution
elsewhere; consequently the document presents a proof of the stated problem
without certifying first discovery.
