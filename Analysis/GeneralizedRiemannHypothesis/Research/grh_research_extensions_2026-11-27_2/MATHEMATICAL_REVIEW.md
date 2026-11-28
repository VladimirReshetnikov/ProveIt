# Independent mathematical review

Reviewed against the 533-line research draft and the repository source at commit `2e714ce3d8e33aa8160391cf5dd95f3af3c34045` on 27 November 2026.

## Spectral quantile theorem

An independent derivation reproduced the conditional rate, the optimizer, and the phase transition. No mathematical gap was found in the stated fixed-parameter result.

The following points were checked in detail:

1. The normalized cumulant generating function is finite on its stated domain, has strictly positive Hessian, and has gradient onto the positive quadrant. The finite-dimensional large-deviation argument follows directly from exponential tilting; it does not require a local limit theorem.
2. The conditional likelihood contains the term `exp(theta N(u) (s-mu_u))`. Keeping that term gives the rate `I-s+C`. Dropping it would give the wrong rare-conditioned total mass.
3. The exact saddle boundary `mu_u` converges to `C`. Strict interior perturbations justify the lower bound even if its convergence is slower than the central-limit scale.
4. The general regular-variation parameters `alpha,p` give the integration-by-parts coefficient `p/alpha`, the constant `D=(p/alpha-1)C`, and the total-mass exponent `p-alpha` as stated.
5. The constrained minimizer is unique. The quantile constraint is active. The total constraint is active below the critical cutoff and inactive above it.
6. The full profile follows from a uniform likelihood bound on the rare event and exponential concentration under a further tilt. A finite mesh and monotonicity give uniform convergence; an infinite-dimensional large-deviation principle or a functional CLT is not being assumed.
7. The first derivatives of the rate agree at the transition. The difference of the second derivatives is the stated strictly positive quantity, obtained from the Schur complement of the Hessian.

For the median with `alpha=1,p=2`, an independent numerical evaluation gave the following values (rounded here to avoid implying more precision than the independent floating-point evaluation provided; the separate 70-digit computation is in `data/verification.json`)

- `c_star approximately 1.626121264897`;
- `K_star approximately 1.205197570560`;
- `R(c_star) approximately 0.389001071095`;
- the left second derivative at the transition approximately `1.77364288228586`, while the right second derivative is zero.

An additional normalization check is exact: `R''(1)=4 pi/(pi^2-4)`. Its reciprocal, divided by `theta N(u)`, agrees with the median-height variance in the repository's existing central-limit theorem.

## Arithmetic scope correction

A reciprocal completed-L-function interpretation requires an even completed product. The arithmetic corollary should therefore use zeta and real primitive Dirichlet characters, with central zero factors removed. A conjugation-closed family of complex characters with matching multiplicities is another valid setting, but an arbitrary unpaired complex-character family does not give that identification. The deterministic-spectrum probability theorem itself does not need RH or GRH.

## Limits of verification and novelty

The result treats fixed `tau`, fixed cutoff `c`, a fixed spectrum, and fixed shape parameter. It does not assert uniformity in growing conductor or degree, a critical-window limit law, finite-saddle error bounds, or a Lean formalization. Numerical checks support the formulas and implementation; the proof establishes the infinite-spectrum theorem.

The audited repository already contains the typical profile and median CLT. The fixed-deviation quantile rate, its change in the active total-mass constraint, and the corresponding rare-conditioned profile were not found there. A limited primary-literature search found classical small-deviation and Gibbs-conditioning antecedents but no exact match for the explicit transition. This review does not certify worldwide priority.

## Symplectic companion

The complete 274-line companion source was independently reviewed. No mathematical gap was found in its stated range: nondegenerate source and target, at least as many complementary symplectic pairs as source pairs, and integer rings of finite extensions of the p-adic numbers.

The normalization `beta_(v,r)` agrees with the count of symplectic embeddings obtained from the quotient of the two symplectic-group orders. The Hall-polynomial Gram density matches Wakatsuki's Theorem 4.3 on the rendered primary-source page 472. The strict sign inequality remains valid in the limiting case `q=2,v=r` because the finite-product bound is strict. Averaging the full density over each residue class preserves its sign relative to one, so the same test realizes total variation at every precision.

The finite-field Fourier transform, its recurrence, rank-orbit reciprocity, and the Gaussian-binomial formula for the nonsingular residual probability were independently derived. Direct exhaustive checks gave:

| q | Target pairs a | Source pairs r | Nonsingular residual probability |
|---:|---:|---:|---:|
| 2 | 1 | 1 | 5/8 |
| 3 | 1 | 1 | 19/27 |
| 2 | 1 | 2 | 17/32 |
| 3 | 1 | 2 | 163/243 |
| 2 | 2 | 2 | 469/1024 |
| 2 | 1 | 3 | 65/128 |

The passage from finite congruence laws to the p-adic density loses no singular mass: the exceptional Pfaffian zero set is null under independent entries and under the smooth symplectic-frame law. On each nondegenerate elementary-divisor orbit the classical density is constant and finite averages stabilize locally.

The proposition about unequal priors is also correct. Residual types `(1,0,...)` and `(2,0,...)` occur on positive-measure sets with the same first residue and different likelihoods. A threshold between those likelihoods gives a strictly better test with three digits. Thus the companion correctly states precision invariance for equal-prior testing of one block and does not claim statistical sufficiency or invariance for arbitrary decision problems.

## Final literature overlap refinement

The finite-field residual probability in the companion is exactly the normalized complement count of De Boeck and Van de Voorde, Theorem 4.6 (Linear Algebra and its Applications 699 (2024), 367–402; DOI 10.1016/j.laa.2024.07.004). The alternating Fourier eigenvalue is also classical, from Delsarte–Goethals (1975). Both are now explicitly credited in the paper. The contribution claimed is the all-precision likelihood-sign theorem and its testing consequences, not those counting ingredients. Targeted checks of related p-adic Haar truncation and additive alternating-matrix literature found no identical combined theorem, without certifying worldwide priority.

## Final source and presentation review

The root reviewer read both complete LaTeX proofs. The spectral summation lemma was made explicitly locally bounded, the curvature statement now names the right-hand second derivative, and the arithmetic statement excludes principal Dirichlet factors because the zeta factor is represented by the entire xi function. All three changes are included in the final paper. Both PDFs were compiled from the packaged sources; final builds have no unresolved references, overflow boxes or LaTeX warnings. All 24 pages were inspected as rendered images, with additional full-page and figure inspections.
