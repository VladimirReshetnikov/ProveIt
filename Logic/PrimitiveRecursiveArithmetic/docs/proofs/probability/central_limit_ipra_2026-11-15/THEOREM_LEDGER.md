# Statement-by-statement coverage ledger

`P` = proved in the manuscript for finite rational presentations, with a direct iPRA arithmetization.

`E` = proved for an effective version with explicit primitive-recursive moduli or for a substantial constructive subclass.

`C` = the source wording needs correction or an additional hypothesis; the corrected theorem is proved.

`O` = not proved in this packet; the reason is stated.

| Source statement | Status | Constructive result in this packet |
|---|---:|---|
| Classical iid CLT with finite positive variance | E/P | Direct `P` for finite rational laws; `E` for arbitrary effectively presented laws with a PR second-moment tail/quantization modulus. |
| Sample-mean form and variance `sigma^2/n` | P | Exact finite expectation/variance identities, followed by the CLT. |
| Pointwise CDF convergence | P | Stronger universal rational-threshold inequality. |
| Uniform CDF convergence | P | Explicit Berry--Esseen bound; no supremum object is needed internally. |
| Characteristic-function proof | P | Finite Taylor remainders, damping by an independent copy, product telescoping, and constructive Esseen smoothing. |
| Berry--Esseen `O(n^-1/2)` rate | P | Constant `64`: `d_K <= 64 rho/(sigma^3 sqrt n)` for every finite rational iid law. |
| Non-identically distributed Berry--Esseen theorem | P | Finite triangular-array form `d_K <= 64 sum E|X_j|^3/s^3`. |
| Lyapunov CLT, especially `delta=1` | P/E | `delta=1` follows immediately from Berry--Esseen; every fixed positive rational `delta` follows through quantitative Lindeberg. |
| Lyapunov implies Lindeberg | P | Pointwise inequality `Y^2 1{|Y|>eta} <= eta^-delta |Y|^(2+delta)`. |
| Converse Lyapunov implication fails | P | Explicit rational triangular array: Lindeberg holds, while the third-moment Lyapunov sum diverges. |
| Lindeberg--Feller CLT | P/E | Quantitative theorem: if `L(eta) <= lambda^3`, then `d_K <= 28 eta + 3 lambda`; effective moduli give convergence. |
| MathWorld claim that finite variances alone suffice for arbitrary independent addends | C | False without an infinitesimal/Lindeberg condition. A one-Rademacher-per-row counterexample is given; the corrected Lindeberg theorem is proved. |
| MathWorld claim that the unnormalized average *is* normally distributed | C | Corrected to *asymptotically* normal. Exact normality is proved for Gaussian summands. |
| MathWorld infinite power-series/Fourier derivation | C/P | Replaced by a finite second-order Taylor formula with explicit third-order remainder; no interchange of an infinite series and integral is used. |
| de Moivre--Laplace/binomial CDF approximation | P | Bernoulli instance of the iid Berry--Esseen theorem. |
| Local de Moivre--Laplace theorem | P | Explicit Robbins--Stirling log-relative error on every central window `|k-np| <= A sqrt n`. |
| Convolution interpretation | P/E | Exact convolution identity for finite laws; a constructive aperiodic lattice local limit theorem is proved with a supplied/computed spectral-gap certificate. |
| Characteristic functions multiply under convolution | P | Exact finite product-space calculation. |
| Multidimensional CLT | P/E | Every rational projection has an explicit scalar Berry--Esseen bound; fixed-dimensional Gaussian-continuity boxes follow by tensor-product smoothing. |
| Convex-set multivariate `C d^(1/4) gamma` rate | O | Requires a separate high-dimensional convex-geometric smoothing theory; only projection and fixed-box results are developed. |
| Robbins random-number-of-summands CLT | E | Effective finite-support version with a PR modulus for the CLT of `N_n`; nonnegativity constructively forces `E N_n/sqrt(Var N_n) -> infinity`. |
| Strong-mixing CLT on the page | E | Proved for bounded stationary `m`-dependent laws, a constructive subclass with mixing coefficient eventually zero. |
| Covariance-series variance formula | P/E | Exact finite-range formula `Var S_n = n sigma^2 - 2 sum h gamma_h`; weighted finite-range version is also proved. |
| Martingale-difference CLT | E | Finite probability trees with PR moduli for predictable variance and conditional Lindeberg tails. |
| Generalized CLT/stable-law characterization | E/O | Gaussian and Cauchy stability and the easy stable-to-limit direction are proved. The full only-if classification is not reconstructed. |
| Normal distribution is stable | P | Exact characteristic-function identity. |
| Relation to the law of large numbers | P | Chebyshev weak LLN with explicit modulus and a finite-horizon maximal form; CLT identifies the next `sqrt n` scale. |
| Entropy increases monotonically | O | Requires differential entropy and the entropy-power machinery; it is not valid without substantial regularity hypotheses. |
| Products of positive variables approach log-normality | P/E | Correct condition: finite variance of `log X`; finite positive rational laws get an explicit Berry--Esseen rate at every positive rational product threshold after taking logs. |
| Wikipedia density-square-integrability wording for products | C | Not the minimal CLT hypothesis. The packet states and proves the finite-variance-of-log formulation. |
| Pairwise independence can replace independence | C/P | It cannot. An explicit `F_2^m` character row gives pairwise independent Rademachers whose normalized sum converges to zero, not normal. |
| Universal sample-size rule such as `n >= 30` | C/P | Refuted by an exact rare-spike finite law with more than `0.997` probability of all zero observations at `n=30`. |
| Dice-sum illustration | P | Direct finite-law corollary, with exact moments and executable diagnostics. |
| Regression error as a sum of small effects | E | Valid under a displayed Lindeberg/Berry--Esseen certificate, not merely by verbal appeal to “many effects.” |
| Convex-body, lacunary-series, Gaussian-polytope, Haar-orthogonal, subsequence, and crystal-lattice CLTs | O | These use distinct geometric, harmonic, or compactness arguments and are not consequences of the finite-sum engine alone. |
| “Fuzzy CLT”/universality slogan | P as a theorem schema | Made precise by the Lindeberg theorem: microscopic laws disappear when no summand retains macroscopic variance. |

The manuscript uses “proved in iPRA” in the proof-theoretic sense explained there: every theorem is a first-order schema for fixed PR presentations and explicit moduli. The archive does **not** claim a completed kernel-checked Lean derivation; that endpoint is specified in `lean/ObjectLanguageTarget.lean` and `lean/ROADMAP.md`.
