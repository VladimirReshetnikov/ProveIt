# Claim ledger

All theorem numbers refer to `article.pdf` and `article.tex` in this package.
"Proved" below means a conventional proof is supplied, not an independent
referee report or a proof-assistant check.

| Assertion | Location | Proof and validation status |
|---|---|---|
| Known-variance scale minimax rate n^(-1/(4m)) | Theorem 2.1; Sections 8–9 | Matching constructive upper and two-point likelihood lower bounds proved. |
| Unknown-variance scale minimax rate n^(-1/(4m+4)) | Theorem 2.1; Sections 8–9 | Matching upper and lower bounds proved. Fixed m and positive bounded variance interval required. |
| Variance minimax rate n^(-1/(2m+2)) | Theorem 2.1; Sections 8–9 | Same hard pair gives a nonzero variance separation; plug-in upper bound proved. |
| Detection exponents 1/8 and 1/4 | Theorem 2.2; Section 10 | Uniform cumulant test plus simple-pair Hellinger lower bound proved. |
| Shifted-moment exponent 1/(m+r) | Theorem 4.1; Sections 4–5 | Universal sign-counting upper bound and exact-fibre sharpness proof. 7,000 rational examples additionally checked. |
| Half-length exponent 1/(2m+2r) | Corollary 4.2 | Square-root upper bound and scaled positive-node sharpness proved. |
| Exact generalized tangent identities | Lemma 5.1 | Lagrange interpolation proof; 40 exact finite instances checked. |
| First-power-sum coefficient flow | Proposition 5.2 | Formal-series and real-root continuation proof; eight symbolic cases with rational root certificates checked. |
| Finite-cumulant identifiability | Proposition 6.1 | Derived from shifted-moment injectivity and the second cumulant. |
| Sharp Hellinger inverse exponents | Theorem 6.2 | Uniform moment bounds for the upper estimates; likelihood pairs for sharpness. |
| Positive weighted derivative information | Lemma 7.1 | Conditional Cauchy–Schwarz and Gaussian Hermite integral; strict positivity proved. |
| Full likelihood asymptotics | Theorem 7.2 | Weighted L2 Taylor expansion, common lower envelope, Fourier identification, and denominator-limit argument proved. Not numerically certified by the script. |
| No uniform exact factor-count consistency | Corollary 10.1 | Consequence of detection lower bounds, without a minimum positive scale. |
| Two-factor rational leading coefficients | Section 11.1 | Exact symbolic calculations in the article and program. |
| 80-digit Fourier convergence diagnostic | Section 11.3 | Numerical illustration, not interval-certified and not a statistical risk experiment. |
| Mixed-stratum formula (13.1) | Research question 2 | CONJECTURAL. Only the fully vanishing and regular cases are established here. |
| Unsmoothed up-law sampling rates | Research question 1 | OPEN IN THIS ARTICLE. No transfer of the Gaussian likelihood proof is claimed. |
| Efficient general-purpose estimator implementation | Research question 4 | NOT DELIVERED. The finite-grid estimator proves attainability, not practical optimal complexity. |
| Lean/Rocq formalization | Section 12.2 | ROADMAP ONLY. No formal verification is claimed. |

The bounds are global over the specified compact parameter set. Their constants
are not asserted uniform in growing m or as the Gaussian variance approaches
zero. Detection at the critical order, consistency above it, and estimation
of an entire factorization are explicitly distinguished.
