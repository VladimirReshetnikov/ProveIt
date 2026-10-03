# Mathematical review of A113226 proof

Reviewed 1 October 2026. Proof revision SHA-256:
5398b71cc6d65d66424f3246ffdcaaa51b587fd6b028ca724199bc9318f2d2ec

No unresolved mathematical defect found in this revision. This is a proof review and independent coefficient verification, not formal verification, conventional peer review, exhaustive priority checking, or finite-target interval certification.

## Checks

- Continuous-label transfer: block factorials, order-chamber volumes, and the unrestricted final zero block produce exactly the exponential generating function. The future state is the maximum of earlier zero labels; earlier one labels impose no further condition.
- The formal operator adds at least two labels, ensuring unique solution. The Volterra equation and its terminal condition give the displayed exponential integral with the correct sign.
- Elementary arcsine form and first-order linear ODE were independently derived. The cumulant relation to A136127 follows by an exact beta integral applied to the known type-C poly-Bernoulli bivariate EGF; attribution is appropriate.
- Analytic continuation follows from the linear ODE on the slit disk; the only nearest coefficient singularity is rho=log4. The regular part of L near rho is analytic after cancellation of its square roots, so its convergent Puiseux expansion has no logarithmic term.
- Minor arcs: the circle's t-coordinate has Re t>=t0. Local quadratic loss controls angles through epsilon t0, the modulus bound gives fixed fractional loss beyond it, and ODE continuation bounds the remaining compact arc. The vertical replacement's connectors differ by O(t0²), incurring only O(n t0²), too small to overcome the fixed phase loss.
- All-orders remainder: on the logarithmic Gaussian cutoff the exponential perturbation has an integrable Gaussian majorant; finite analytic Taylor remainders have polynomial Gaussian bounds. Symmetry eliminates odd half-orders. Thus no omitted logarithmic factor enters the stated O(n^(-(J+1)/3)) remainder.
- Independently hand-expanded the first four half-order perturbation polynomials and integrated their Gaussian moments in root_coefficient_audit.py. Both a1 and a2 match the proposed formulas exactly. This check does not import the author's generator.
- Inverse substitution: the coefficients at N^(1/3), 1, N^(-1/3), N^(-2/3) cancel as claimed. The remaining logarithmic residual is O(N^-1); derivative comparable to ell gives O(1/(N ell)). The smooth realization construction is noncanonical but flat differences preserve all orders. Integer threshold envelopes correctly avoid unconditional rounding of an o(1) approximation.

## Scope retained
The report proves a fixed-order Poincare expansion to arbitrary order. It does not establish convergence, complete exponentially small sectors, a canonical analytic interpolation, or explicit certified finite-n error constants. Existing combinatorial bijections, A136127 and its leading asymptotic must continue to be credited. A separate expert's review is advisable before journal submission.
