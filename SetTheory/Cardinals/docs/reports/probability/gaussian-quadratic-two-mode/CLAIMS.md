# Claim ledger

**Status:** unrefereed manuscript with proofs and reproducible diagnostics;
no independent review, no Lean certificate, no established priority claim.

## Results proved in the manuscript

| Result | Exact scope | Proof location |
|---|---|---|
| Sharp coefficient interval | Real finite spectrum; second sum 1 and third sum delta imply -b <= c_i <= a | Lemma 3.1 |
| Feasible endpoint chord | Convex functions of the squared-coefficient probability measure | Lemma 3.2 |
| Fourth-convex extremality | C^2 f with convex f'' and polynomial growth of f,f',f'' | Theorem 2.1; Section 4 |
| All absolute moments p >= 3 | Fixed variance and fixed skewness, arbitrary real coefficients, all equality cases | Theorem 2.1 |
| Sharp skewness-kurtosis frontier | Every delta in [-1,1], attained rank two or endpoint rank one | Theorem 5.1 |
| Zero-skewness exact constants | sqrt(2) times a product of two independent standard normals is extremal | Corollary 5.2 |
| Quantitative moment deficits | Explicit positive lower constants for every p > 3; exact coefficient 48 at p=4 | Theorem 6.1 |
| Spectral rigidity | Zero-padded spectrum distance; explicit K_delta for interior delta | Theorem 7.1 |
| Optimal zero-skewness rigidity constant | D^2 <= 4 Delta_4 uniformly in dimension; 4 is optimal | Theorem 7.1 |
| Sharp distance exponent | Square-root distance dependence on fourth-moment deficit cannot improve | Section 7.1 |
| Attained Laplace envelope | Full common domain -1/(2b) < t < 1/(2a) | Theorem 8.1 |
| Closed-form Chernoff optimizer | Right tail x >= 0, with separately handled endpoint cases | Section 8.1 |
| Best exponential tail scale | Fixed interior delta; matching asymptotic of the admissible extremizer | Proposition 8.2 |
| Failure of pointwise tail domination | Explicit variance-two zero-skewness Laplace example | Section 9 |
| Common-shape Gamma extension | All positive shapes, same test class, p >= 3 equality cases | Theorem 10.1 |
| Infinitely divisible extension | Centered common base with a finite two-sided exponential moment | Proposition 10.2 |
| Countable Gaussian modes | Square-summable normalized coefficients; comparison and moment bound | Corollary 10.3 |

## Claims deliberately not made

1. This is not an independently established breakthrough or a priority-certified
   first proof. A broader literature audit is still needed.
2. The unconditioned p in [3,4) problem is reduced to a scalar problem, not solved.
   The conditioned p in (2,3) problem is not solved here.
3. Fourth-convex order is not ordinary stochastic order or ordinary convex order.
   The article gives a counterexample to the tempting tail substitution.
4. A sharp Laplace supremum does not make its Chernoff tail bound pointwise exact.
   Only the exponential scale is claimed optimal for the tail bound.
5. The general infinitely divisible extension does not inherit the strict
   equality classification. A Gaussian base is an immediate obstruction.
6. If the base law has zero third cumulant, the coefficient cubic sum is not
   identifiable from skewness. It is additional information in Proposition 10.2.
7. Spectral rigidity permits zero padding. It is not silently asserted as the
   same unpadded orbit distance for a one-sign full-rank matrix.
8. The trace-estimator bound does not use all repeated-block information and is
   not asymptotically sharp in sample size for a fixed matrix.
9. There is no claim for noncentral quadratic forms, arbitrary non-Gaussian
   inputs, interacting spin systems, or quantum observables without the stated
   distributional hypotheses.
10. Exact finite tests and numerical quadrature are not general proof
    certificates, interval certificates, or Lean formalizations.

## Computation and novelty audit

The exact identities are independently encoded in integer/rational algebra.
The numerical checks include nonsymmetric zero-skewness spectra and non-integer
moments. A cancellation bug in an evaluation formula was found and corrected;
it did not invalidate the symbolic saddle equation or the comparison proof.

The closest source examined, Pang (arXiv:2609.05914v1), provides a Gamma envelope
from the global interval [-1,1]. This manuscript explicitly credits the shared
chord and Poisson-interpolation architecture. Its proposed strengthening uses
the sharp interval [-b,a] implied by the two coefficient sums, making the
comparison law feasible and its bound attained. That is the precise novelty
claim to audit, rather than an unsupported claim to have invented higher convex
order or Gamma interpolation.
