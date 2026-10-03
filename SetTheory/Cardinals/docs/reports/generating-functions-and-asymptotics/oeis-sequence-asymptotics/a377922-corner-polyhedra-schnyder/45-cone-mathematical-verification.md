# Mathematical verification report

Manuscript: *Polynomial exponents for corner polyhedra and Schnyder labelings*

Review date: 2 October 2026

## Conclusion

No unresolved mathematical error or missing hypothesis was identified in the reviewed source. The integrated argument supports the following results:

- A377922: p_n = Θ((9/2)^n n^(-α_P)), where α_P = 1 + π/arccos(9/16)
- A377920: s_n = Θ((16/3)^n n^(-α_S)), where α_S = 1 + π/arccos(22/27)
- Both estimates hold for every sufficiently large integer n
- The generating functions of A377922, A377920, and A377921 are not D-finite
- The first-threshold inverses have the stated log Y + α log log Y expansions, with O(1) error and without a monotonicity assumption

This is a mathematical review supported by exact computational checks. It is not machine formal verification, external journal peer review, or a publication-priority determination.

## Exact source reviewed

File: article.tex

SHA-256: 849e515056a5b296221d6fe1a0ca09c1a7fd78a19d776256ee25143070128bb2

The manuscript is self-contained: it has no included mathematical source files or external bibliography files. Its bibliography is embedded in article.tex. The accompanying JSON receipt records exact source and supporting-check hashes. Changes to the mathematical source require a fresh review.

The PDF is identified in the receipt for delivery consistency. PDF rendering and visual-layout verification are outside the scope of this mathematical report.

## Proof components checked

1. **Counting models and normalization.** The P-admissible walk has physical length n and the exact endpoint sum includes 3^(-i). The S-admissible walk has n+1 aggregates after removal of its final southeast step, with the required factor 1/4. The conversion from s'_n to s_n uses the source's valid index range.

2. **Schnyder boundary equivalence.** Restricting aggregate endpoints to x ≥ 0, y ≥ 1 is equivalent to physical quadrant survival for the relevant fixed-endpoint walks. The initial southeast step and the monotonicity of each subsequent face string control all intermediate physical positions.

3. **Regeneration and covariance.** The first-return cycles are iid at either starting parity. Their means, nondegenerate covariances, duration moments, exponential moments, and forward/reverse bounded correctors are consistent with the displayed kernels. The spatial covariance is normalized per counted step. Duration and displacement dependence is retained throughout.

4. **One-unit cycle buffer.** The deterministic minimum-minus-one bound controls every intermediate cycle position. It also holds under reversal. Keeping even skeleton endpoints at coordinates at least two therefore supplies genuine model-time survival. This implication is used in the lower bound; the upper bound uses only the reverse event inclusion.

5. **Applicability of the iid cone theorem.** The cited Denisov–Wachtel results are used only for the iid skeleton. Centering, exponential moments, covariance normalization, wedge geometry, harmonic-function comparison, and accessibility are checked. The required p ≥ 1 hypothesis is explicit. Boundary translations occur before whitening.

6. **Exact-time transfer.** The clock is placed beyond n in a window of length O(n^(3/4)). Unconditional Chernoff and martingale maximal bounds have errors exponentially smaller than the polynomial cone mass. Subtracting those errors does not require independence of cycle duration and displacement or any conditioned concentration theorem. Nested fixed balls account for every time ratio and fixed entrance length.

7. **Lattice and local estimates.** The translation-cell Fourier matrix has no secondary unit-modulus points. Both coordinate support differences and the internal-chain spectral gap are checked. The local limit factor two is the physical lattice covolume. Every initial/final parity pair and every sufficiently large integer time is covered.

8. **Killed middle kernel and gluing.** A free Gaussian lower bound is reduced by first-half exits and reversed second-half exits. The uniform free upper bound and quadratic martingale maximal inequality control the discarded mass. The resulting killed lower bound is of order 1/n. The upper endpoint sum is summable against its exponential weight; the lower bound uses fixed valid endpoints.

9. **Non-D-finiteness.** Both exponents are irrational by the root-of-unity/algebraic-integer argument. The positive-derivative comparison converts a Θ coefficient estimate into an irrational singular growth exponent, contradicting the rational-power/logarithm local structure of a G-function. This supplies the additional argument needed beyond criteria that assume a full asymptotic equivalent. The exact rational generating-function identity transfers non-D-finiteness to A377921.

10. **Threshold inversion.** Eventually increasing exponential-polynomial upper and lower comparison functions bracket the first crossing within a bounded interval. Monotonicity of the counting sequence itself is unnecessary.

## Reproducibility checks

The supplied scripts/run_all.py was rerun successfully. All four verification programs exited with code zero. Checks include exact kernel/corrector/covariance identities, both parity return laws, the S face resolvent, 25,900 bounded P-cycle configurations and their reversals, independent P coefficients through n = 15, independent S aggregate coefficients through n = 14, and the longer S recurrence comparison through n = 30. The recorded outputs agree with the displayed initial coefficients and supplied OEIS export.

These finite computations corroborate identities and indexing. They do not replace the proof of the unbounded cycle lemma, the probabilistic estimates, or the cited theorems.

## Scope that remains unresolved

The bounds do not establish convergence to positive amplitude constants, compute those constants, or prove the full asymptotic equivalents in Conjecture 25. They do not provide a coefficientwise Θ estimate for A377921. The threshold estimates do not determine an exact rounding rule or the next additive constant. These limits are correctly retained in the manuscript.

## Principal mathematical dependencies

- Fusy–Narmanli–Schaeffer, published walk bijections and exact counting relations: https://arxiv.org/html/2202.09172v3
- Denisov–Wachtel, *Random walks in cones revisited*, Theorems 2–3: https://arxiv.org/html/2112.10244
- Fischler–Rivoal, *On the values of G-functions*, Definition 1 and Theorem 6: https://doi.org/10.4171/CMH/321

The manuscript distinguishes these established inputs from its fixed-buffer, exact-time-transfer, and gluing arguments.
