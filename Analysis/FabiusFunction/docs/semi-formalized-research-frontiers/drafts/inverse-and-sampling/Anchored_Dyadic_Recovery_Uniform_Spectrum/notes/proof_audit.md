# Claim and proof audit

## Proven scope

The anchored modulus is exp[-Theta(sqrt(log(1/epsilon)))] for both total
variation and Kolmogorov distances, on A_L (L > 1), the predecessor's class K,
and K_rho for 1/2 < rho < 1. The leading logarithmic constant is bracketed,
not identified. Every fixed leading prefix is Lipschitz-stable on A_L, L >= 1.
The statistical lower bound concerns testing and honest local inference;
it is not a nonsensical risk bound for an estimator evaluated only at a known point.

## Upper proof: important checks

1. Summability gives entire characteristic functions and an exact multiset of
   real zeros. Infinite products add no extra zeros: the remaining logarithms
   converge locally after removing finitely many factors.
2. Both law metrics control transform errors on the same bounded-height
   contours. The compact support bound is essential, particularly for the
   integration-by-parts Kolmogorov estimate. Endpoint atoms cause no boundary
   term when integration first takes place on a larger interval.
3. Rouché supplies counts on disks, not individual root locations. A separate
   real-axis lower bound rules out unwanted roots in the gaps and near zero.
4. Every unknown uniform factor contributes a complete harmonic progression.
   Its progression cannot change nearest-integer phase between consecutive
   observed harmonics because 3 eta < 1. The resulting triangular divisor
   system, not generic multiple-root continuity, recovers primitive periods.
5. Prefix Lipschitzness uses the sum of zeros in each cluster and the recursion
   beta_j = S_j - 2 S_(j-1). The logarithm of the transform ratio exists on a
   neighborhood of the contour, not necessarily in the disk interior. This
   is enough for contour integration by parts and avoids an invalid global log.
6. Integer floors and ceilings in M are absorbed by constant factors, not by
   changing the square-root logarithmic exponent.

## Lower proof: important checks

1. P_n - Delta_n has one simple positive root in each stated interval. The
   proof uses signs at both endpoints, with the perturbation smaller than
   the endpoint modulus, and exhausts the polynomial degree.
2. Perturbed even factors stay between their unchanged odd neighbors.
   No unnoticed resorting or factor-rank change enters the spectral loss.
3. Newton identities preserve power sums through n-1, hence law moments through
   2n-1. The nth power-sum change is exactly n Delta_n. The variance is exact.
4. The last factor changes by at least (tau/3) 4^(-n); the full l1 change is at
   most 3 tau 4^(-n). The comparison is directly with the exact dyadic law.
5. The prefix product of coefficient ratios stays above one-half at every
   prefix. Together with the exact derivative norms of the dyadic density,
   this proves all of K's derivative bounds with its original constants.
6. Tau can be decreased for any rho > 1/2 without changing the n^2 law-error
   exponent. No result is claimed at rho = 1/2 itself.
7. The common characteristic-function factor includes both the unchanged odd
   spectrum and the unchanged even tail. Only the modulus of the latter is
   discarded; it is not silently deleted from an exact identity.
8. Head and tail are treated separately. Only the small tail has sinc arguments
   below pi up to the frequency cutoff. Its real logarithm is therefore valid;
   no expansion is pushed through a sinc zero.
9. High frequencies use an independent envelope from the unchanged odd factors.
   The low-frequency cancellation is never presumed valid beyond its cutoff.
10. Plancherel is converted to total variation using the actual common support
    containment [-2,2]. The factor 1/(2 pi) follows the characteristic-function
    convention. There is no unsupported passage from moment matching to TV.

## Statistical steps

The upper test uses a uniform empirical-CDF error bound plus the finite inverse
certificate. The lower bound uses the exact-null alternative and product TV
<= N times one-sample TV. The usual one-sample DKW–Massart inequality is an
explicit external input. Confidence coverage is global, while the asserted
contraction is at the dyadic reference. Infinite-dimensional confidence sets
are theoretical objects here, not a supplied finite representation algorithm.

## Actual checks and limitations

The included program passed 949 finite rational checks and completed the
separately labeled mpmath diagnostics. Neither proves the analytic theorems.
The PDF was compiled with references resolved, rendered, and visually inspected;
see validation.json. No Lean/Rocq build or independent review was performed.
No claim of exhaustive novelty priority is made. The predecessor's pairwise
modulus and exact-support-endpoint questions remain distinct and unresolved.
