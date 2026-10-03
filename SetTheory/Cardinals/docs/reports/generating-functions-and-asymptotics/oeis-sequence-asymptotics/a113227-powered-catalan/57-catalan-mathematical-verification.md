# Mathematical verification record

Reviewed 1 October 2026.

## Version reviewed

Source: `powered-catalan-asymptotics.tex`

SHA-256: `2feb8e8de0603df2b8c47ef892caccf7d5bacfb542559f706039ce787eb7382a`

Corresponding PDF: `powered-catalan-asymptotics.pdf`

SHA-256: `f3f0c49f9b06b773120250b33eda2092b342c79f04cd526df0ad8800f3084454`

## Conclusion

No blocking mathematical error was found in this version. The report faithfully contains the checked positive spectral representation, leading equivalent, arbitrary fixed-order expansion, canonical continuous inverse, and positive-real-axis exponential-generating-function asymptotic. The review consisted of direct mathematical examination, independent symbolic calculations, and numerical diagnostics. It is not a proof-assistant verification or an external peer-review certification.

## Mathematical checks

1. **Known sequence and formal starting point.** The valley-marked path convention, reversible conversion to weighted Schröder paths, recurrence, and formal continued fraction have the correct indices. The exceptional root shift in the finite rational recurrence is essential and is retained. Attribution distinguishes these known starting points from the results established in the report.

2. **Positive finite measures and their limit.** Interlacing, positive residues, and the normalization at zero correctly give probability measures for every truncation. Tightness and uniform integrability give all limiting moments. The bound `a_n <= n!` justifies exponential-moment determinacy, so the limit is unique.

3. **Global analytic identification.** The negative-axis modified-Bessel recurrence selects the correct branch by a direct contraction argument. The normalized numerator and denominator are entire and have no common zero. Their identification with the Stieltjes transform rules out nonreal poles, higher-order poles, continuous mass, an atom at zero, and an omitted entire contribution. The resulting spectrum is positive, discrete, and bounded away from zero.

4. **Large nodes and positive weights.** The Schläfli substitution and its total parameter derivative have the stated signs and factors. Gamma localization controls both tails. The Bessel Wronskian gives the positive residue formula, including its factors of pi. Monotonicity of the tangent equation proves completeness of the sufficiently high nodes. Their displacements are negligible at every algebraic moment order.

5. **All-orders remainders.** The reciprocal-product series are correctly treated as formal coefficient generators rather than convergent sums evaluated at reciprocal integers. Truncated gamma integrals, factorial tails, and uniform product remainders justify each fixed residue order. The exact saddle localization identity controls the exterior; normalized central Taylor coefficients remain bounded as the Lambert parameter grows. Euler–Maclaurin with sufficiently many derivatives gives a lattice error smaller than any specified algebraic order.

6. **Coefficient formulas.** The Bernoulli correction, Gaussian coefficient algorithm, displayed rational functions `c_1` and `c_2`, and the denominator/degree bounds agree with the derivation. Independent expansion gives the additional cancellation

   `a(t)/(P(t)e^(-1)) = t^(-2) + (3/2)t^(-3) - (97/24)t^(-4) + O(t^(-5))`.

   The printed coefficient values `alpha_1 = 5/6`, `alpha_2 = 73/72`, `alpha_3 = 11821/6480`, and `alpha_4 = 702533/155520` match the symbolic generator. The Bell-polynomial normalization constant is `0.818193265211777061027107...`, as reported.

7. **Continuous inverse.** Entirety of the interpolation follows from the positive minimum of the support and its finite positive moments. Strict log-convexity and Jensen's inequalities put its unique minimum in `(0,1)` and justify the increasing branch on `[1,infinity)`. Convex secant bounds establish the needed derivative estimate without differentiating an asymptotic remainder. Both displayed explicit inverse corrections and their error scales are correct. The discrete-threshold statement correctly assumes `Y > 1`.

8. **Exponential generating function.** The spectral exponential sum is entire. Poisson inverse-moment expansion gives the corrections `67/24` and `11857/1152`. The alternative saddle proof correctly retains a lower cutoff when the auxiliary saddle parameter is zero; its endpoint contributions are negligible. This justifies the coefficients `c_j(0)` to every fixed order. The asserted asymptotic is restricted to the positive real direction.

## Numerical evidence checked

- Finite fractions through height 6 have positive simple nodes and stabilize to the initial powered-Catalan terms `1, 1, 2, 6, 23, 105, 549, 3207`.
- The residue coefficient generator was rerun and reproduced the stated coefficients through the displayed orders.
- The 110-digit spectral diagnostic with 65 nodes was rerun. Its mass agrees with 1 to the printed 50 decimal digits; its relative moment discrepancy is approximately `-1.46e-65` at order 1 and `-1.84e-40` at order 30, consistent with the omitted positive tail.
- The report's recurrence-based table entries and inverse-example figures were checked against their numerical records. In particular, the second scaled residual differs from `c_2(w)` by about `0.243588` at `n=50` and `0.00637971` at `n=2500`. The stated order-2 inverse error at `n=500` is `2.07456244e-7`.

These diagnostics corroborate the formulas. They do not supply certified root enclosures or replace the analytic completeness proof.

## Corrections incorporated during review

- Restored the square-root symbol in the denominator of the unnormalized Bessel quotient.
- Made the positive lower cutoff explicit in the auxiliary zero-parameter saddle proof for the exponential generating function. The uncut inverse-power amplitude would be nonintegrable at zero; retaining the cutoff leaves all coefficients unchanged.

## Limits retained in the report

The all-orders result is a Poincaré expansion, with constants depending on the fixed truncation order. Convergence of the infinite correction series is not asserted. A small numerical residual certifies the truncated inverse equation's root error; a certified enclosure of the true inverse at a particular finite target additionally needs an explicit numerical asymptotic-remainder bound. Numerical scans are not certified interval computations. The literature statement is limited to the sources surveyed and does not establish global priority or repository-wide nonduplication.

The special-function identities were checked against the primary NIST Digital Library of Mathematical Functions, especially [the modified-Bessel recurrence](https://dlmf.nist.gov/10.29.E1), [Schläfli's integral](https://dlmf.nist.gov/10.9.E7), and [the Bessel Wronskian](https://dlmf.nist.gov/10.5.E2).
