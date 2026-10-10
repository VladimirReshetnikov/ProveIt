# Mathematical audit record

The following checks were made during preparation. “Independent” here means a separate derivation or review within this research session, not external refereeing.

## Analytic proof checks

| Component | Main obligations checked | Outcome and scope |
|---|---|---|
| Fractional signed moments | Regularized Hurwitz transform; Gamma normalizations; integrability at both endpoints; strict monotonicity of each rescaled density; critical atom masses; moment uniqueness and excluded-domain necessity | Passed separate audit. The theorem classifies finite real signed measures, not all parameters for zero-free continuation. |
| Complex and angular zeros | Positive measure after multiplication by the crossing factor; nonvanishing of its transform; ordered-kernel uniqueness; derivative sign; atom dominance at the unit-circle endpoint | Passed. Final wording specifies open arcs and Abel values at atomic edges. |
| Boundary scales | Balancing equation, Gamma ratio, relative error, weak convergence and signed-mass convergence; complementary edge; logarithmic-corner mass | Passed. Inner order is fixed in each stated edge asymptotic. |
| Local radial coefficient | Four-mode expansion; exact Bernstein coefficients; rational log bounds; monotonicity of G in outer order; inner-order split and analytic threshold | Independently expanded and checked. Global integer-order monotonicity remains open. |
| Fractional maximum and minimum | Seven-mode Chebyshev expansion; full quartic term including the K correction; exact interval arithmetic; joint analyticity; implicit-function direction and second-derivative sign | Both certificates independently replayed, including every rational endpoint and outward decimal. The turning points are locally unique; no global turning count is claimed. |
| Adjacent-index Bessel limit | Angular Cauchy bound and exponential constant; differentiated spectral tail; elementary-symmetric generating product; uniform control of the infinite coefficient sum; zero coefficient recursion | Passed. Fixed integer r, fixed Bessel label, compact scaled coordinate, all Lerch parameters. |
| Small-rho global zero count | Real-root preserving operator; elementary multiplicities; integer polynomial at transcendental log(2); Puiseux coefficients; complex-branch exhaustion; endpoint and compact-set exclusion | Independently audited. The small-rho interval is pair-dependent and not given an effective lower bound. |
| Joint gamma transition | Exact Gamma expectation; all three full-weight tail regions; shifted moments; local derivatives and inverse-L cancellation; uniform first correction; Lambert-W inversion | Two separate audits found no mathematical error. The algorithm for higher orders is described without claiming unproved coefficient cancellation. |
| Cayley formal quotient | Sign convention for pullback/reversal; admissibility; commuting traces; polynomial shuffle generators; equivariant indecomposable lifts; endpoint correction; Hilbert characters; singularity asymptotics | Passed. The exact presentation omits stuffle and distribution, and does not assert numerical independence. |
| Explicit S-family | Prefix-color/outer-first convention; conjugate grouping; exact word residual; independent Mellin substitution | Passed. The 96-term S6 formula is distinct from the still-conjectural depth-two formula. |

## Finite arithmetic

The provided exact replays use integer Gaussian elimination, rational interval operations, rational polynomial algebra, and exact coefficient generation. The program outputs and JSON endpoints are retained. The fractional certificates include explicit elementary tail bounds; they do not delegate sign decisions to floating-point special functions.

The numerical quadratures, plots, full-function roots and sampled asymptotic ratios are diagnostics. The approximate quartic-sign transition near `b=0.9974937898734204` is not an interval enclosure. Its existence somewhere in `(1/2,999/1000)` follows rigorously from two separately certified signs and analyticity; uniqueness remains open.

## What this record does not establish

It does not prove the S6 depth-two conjecture, global normalized-radius monotonicity in the original integer range, period independence, or exhaustive historical novelty. It does not replace the written proofs, and it is not a proof-assistant certificate.
