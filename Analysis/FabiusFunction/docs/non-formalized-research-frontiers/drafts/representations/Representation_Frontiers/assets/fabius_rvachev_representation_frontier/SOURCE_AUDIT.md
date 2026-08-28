# Source Audit and Novelty-Collision Record

## 1. Audited boundary

The requested boundary was every current `*.tex` document recursively reachable under:

`https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs`

The primary formal exposition used in the report is pinned to:

- commit: `0770442945d65bac5530c4f214c6c52c4cb9fbdc`
- date: 27 August 2026
- pinned tree: `https://github.com/VladimirReshetnikov/ProveIt/tree/0770442945d65bac5530c4f214c6c52c4cb9fbdc/Analysis/FabiusFunction`

The branch changed during the audit. In particular, the newer primary source contained a formal support-free quantile-substitution theorem absent from the earlier snapshot. Quantile pushforward identities were therefore downgraded from prospective novelty to repository consequences.

## 2. Audit method

The audit used four layers:

1. **Recursive inventory.** Current TeX paths and nested draft families were enumerated rather than inferred from the top-level web view.
2. **Canonical-source review.** The primary exposition, consolidated frontier notebook, glossary, Lean walkthrough, non-elementarity discussion, and embedded literature sources were reviewed for definitions, normalizations, formulae, and proof dependencies.
3. **Living-draft collision search.** The active draft root was searched separately because it contains newer spectral, inverse, arithmetic-ray, self-sampling, and endpoint work. One audited draft snapshot recorded 67 distinct TeX paths; the active root contained 17 named document families.
4. **Archive deduplication.** Historical copies were mapped through the repository provenance file. Byte-identical, superseded, or renamed copies were not treated as independent mathematical sources; their living successors were reviewed at formula level.

This process is designed to avoid false novelty caused by a moved file, an unconsolidated draft, or a duplicated archive bundle.

## 3. Principal living draft families reviewed

- `Fabius_Arithmetic_Rays_Frontier_Report`
- `Fabius_Dyadic_Self_Sampling_Frontier_Package`
- `Fabius_Half_Integer_Spectral_Frontier_Report`
- `Fabius_Inverse_Frontier_Report_Source_and_PDF`
- `Fabius_Newton_Rvachev_Frontier_Report`
- `Fabius_Rvachev_Frontier_Report-2`
- `Fabius_Rvachev_Frontier_Report`
- `Fabius_Rvachev_New_Frontiers`
- `Fabius_Rvachev_Thue_Morse_Frontier_Results`
- `Spectral_Arithmetic_Pascal_Rvachev_Hierarchy`
- `Thue_Morse_Formula_Atlas`
- `fabius_frontier_dyadic_inverse_barnes_report`
- `fabius_frontier_new_results`
- `fabius_frontier_results`
- `fabius_frontier_results_bundle`
- `fabius_frontier_spectral_endpoint_report_bundle`
- `rvachev_up_fourier_decay`

## 4. Collision quarantine: results already present

The following attractive formula families were found in the repository and are not claimed as new in the report:

- the infinite sinc product and weighted cosine product for the Rvachev Fourier image;
- the integer-zero canonical product with multiplicity `a_n = 1 + v_2(n)`;
- the arithmetic counting identity `sum_{n<=N} a_n = 2N - s_2(N)`;
- Dirichlet-series, heat-trace, spectral-zeta, lobe-sign, zero-jet, and Fredholm-determinant consequences of that divisor;
- half-integer cosine expansions, sampling formulae, alias identities, and spectral quadrature;
- infinite-uniform convolution, finite box splines, Thue--Morse truncated-power formulae, and exact head--tail decompositions;
- moment/cumulant formulae through Bernoulli and Bell polynomials;
- q-binomial, q-MZV, Newton, Appell, and Barnes-prefix representations;
- endpoint and inverse asymptotics involving lower Lambert-W branches and periodic modulation;
- the generalized-gamma-convolution variable with discrete Thorin measure and complete-Bernstein consequences;
- the independent dyadic logistic-series dual;
- the formal quantile substitution theorem and its direct pushforward consequences.

Several initially promising ideas were removed from the novelty list after these collisions were found. In particular, the arithmetic Weierstrass product, interval cosine series, GGC/Thorin interpretation, and basic quantile product transforms are treated only as foundations.

## 5. Results designated “proved here”

Targeted searches of the audited corpus did not locate the following theorem packages in the forms proved in the report:

### 5.1 Dyadic gamma factorization

Define

`Gamma_dy(z) = product_{h>=0} Gamma(1 + z/2^h)`.

The report proves local uniform convergence away from the negative integers, the Mahler equation, pole multiplicity `1+v_2(n)` at `-n`, the reflection factorization

`Phi(z) = 1/(Gamma_dy(z) Gamma_dy(-z))`,

the canonical product for `1/Gamma_dy`, a power series, dyadic digamma/resolvent identities, Malmsten and heat-trace integrals, and a geometric-q extension.

### 5.2 Gaussian variance-mixture bridge

The report explicitly identifies the existing dyadic logistic series with a Gaussian whose random variance is the existing arithmetic Thorin/gamma-convolution variable. It derives the full `tau` convolution semigroup, normal-mixture density, cumulants, explicit symmetric Levy density, self-decomposability, complete monotonicity in the squared coordinate, and dimension-free radial positive definiteness.

### 5.3 Jensen/factorial/digit-sum bridge

The circular mean of `log|Phi|` is evaluated as both a zero-divisor sum and a finite dyadic factorial product. Its logarithmic radial derivative recovers `2N-s_2(N)`, giving direct complex-analytic access to binary digit sums. A leading asymptotic and a subunit angular covariance kernel are also derived.

### 5.4 Non-D-finiteness

Unbounded zero multiplicities at powers of two are used to prove that `Phi` and `1/Gamma_dy` are not D-finite. Infinitely many finite poles exclude D-finiteness of `Gamma_dy` itself.

### 5.5 Fourier formulae for the bounded CDF and its inverse

The report gives the density transform, compact transforms, the global tempered-distribution transform of the bounded CDF, an odd-harmonic sine series for `F`, and a nonlinear Fourier transform and sine series for `Q=F^{-1}` whose coefficients are oscillatory integrals of `F`.

## 6. Conjectures and research directions

All unproved statements are labeled as conjectures. They include differential transcendence, refined periodic Jensen fluctuations, zero-free half-plane behavior for a centered dyadic gamma factor, phase laws for inverse-Fourier coefficients, and optimal rational approximations. The report also proposes Lean formalization, de Branges/spectral analysis, subordinate-Brownian semigroups, base-b generalizations, certified inverse asymptotics, and interval-arithmetic verification.

## 7. Scope limitation

The audit supports only a **new-to-this-repository-corpus** classification. It is not a claim that no equivalent identity exists anywhere in the broader mathematical literature. External references were used for standard theorems and historical context, but a universal priority search is outside the finite audit boundary.
