# Corrections and guards

The inspected predecessor's first-derivative results were not found false.
The following are precise guards for integrating this continuation.

1. **First-order parity is not a second-order identity.** Even W removes the
   local polynomial, not the Gamma chord. For W=1 the second defect is
   `-4 sum atan(b/(n+a))^2`, nonzero for every positive mass. The all-mass second
   vanishing criterion is exactly W=0.
2. **Keep an extra Taylor coefficient at a pole.** The r-th resonant jet uses
   `d[k,r+1]/2`, not only coefficients through order r. The pole scale is 2s.
3. **Odd weights retain the Gamma correction.** For W=x, Delta_2 equals the
   Gamma chord plus 4b^2. An uncorrected chord formula is false.
4. **Normalize mass antiderivatives.** M_m alone satisfies an inhomogeneous
   ladder. `M_m + 2 H_m L_m` satisfies the homogeneous one. At every order use
   the germ `m! E(t-m)/(1-t)_m` and the stated zero-mass boundary values.
5. **Convergent integrals do not validate divergent sums.** The original
   two-mass logarithm-square sum is ordinary for even W of degree at most 2.
   Higher weights require the specified continuation, evaluated by the
   ordinary beta-chord integral. No positivity inference is justified there.
6. **Do not extend a Taylor disk silently.** Select a finite head with a+N>b
   (or larger than every mass) before using the inverse-power series.
7. **Do not split endpoint subtractions.** The four-term numerator is essential
   for integrability. Use analytic logGamma and the diagonal collision series.
8. **Do not overstate verification.** Exact regressions prove their finite
   algebraic assertions. Numerical residuals are neither tail certificates
   nor bounds on the true error. Analytic proofs and conjecture status remain
   distinct.
