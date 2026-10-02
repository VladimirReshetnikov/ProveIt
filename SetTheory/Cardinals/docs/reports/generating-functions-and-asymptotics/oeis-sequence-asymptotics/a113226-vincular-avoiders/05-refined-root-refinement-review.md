# Review of the parameterized A113226 proof

Reviewed 1 October2026. Input refined-proof.md SHA-256:
a5186ace1f4b23019d6893e0c2a69d872c7b1b3c1f152f25e944ffb8c21a8efb

No material defect found in the stated compact-parameter/interior-density results. This is mathematical review and independent coefficient checking, not formal verification or conventional peer review.

Checks included:
- The marked transfer retains the correct factorial normalization and identifies the statistics specifically through BCK's poset bijection.
- The beta-integral formula for polynomial cumulants has coefficient m!(m−1)!, not m!²; the factor1/m is essential and correctly included.
- Singular coefficient πu^(-1/4), constant K=rho/2−2−u^(-1/2), amplitude and density/variance formulas agree with independent derivation and numerical spot checks at u=1/4,1,4.
- Common complex-parameter domain: strict denominator inequality off the unique real pinch and compactness provide the required neighborhood. The local joint expansion handles the pinch. No false inference from apparent q=−1 branch points is made.
- The approximate complex saddle circle has a residual linear phase, but its O(delta*y) size is negligible on the Gaussian scale and can be absorbed outside the cutoff. The finite scaled endpoint deformation must be understood continuously from real parameters, where the phase loss is strict; the claimed uniform continuation then follows on a sufficiently small complex neighborhood.
- The global marking phase-gap argument uses equality cases in the positive exponential series and correctly excludes other unit-circle marking saddles.
- Both-saddle expansion parity and powers are consistent. An independent hand expansion of the second-saddle exponent verifies b1 and b2 exactly in root_two_saddle_audit.py/json without importing the author's coefficient generator.
- Mean constant, variance positivity, local-limit centering, conditional Poisson correction and covariance were checked. The total-variation estimate follows from uniform holomorphic remainder on a fixed |s|<=R>1 and a summable Cauchy coefficient bound.
- These are uniform only on compact positive u and compact interior k/n. No boundary-density transition, exponentially complete expansion or certified finite-n error bound follows.

The precise refined-count/local-large-deviation formula, including the stretched second-saddle correction, is the substantive addition. The Gaussian and Poisson consequences should remain described as consequences of the parameterized coefficient theorem, with standard methods credited.

## Updated revision review
The added record-to-cycle bijection and the explicit continuous-from-real connector prescription were reviewed in revision SHA-256 62125f46b4ad8cdc0e0f9f871a5e3132da275f0d2a2f45ed5ba514d6fc4a21ec. Both are sound. Each record segment has its first E maximum greater than all later E maxima, while every M exceeds that first maximum; unique rotation and sorting by increasing maxima give the inverse. The count m!(m−1)! of matchings and cyclic orders gives the same component formula, with no binomial choice for E labels because they are the smallest labels of their component. No map to a previously named A136127 object model is claimed. Previous review conclusion is unchanged.
