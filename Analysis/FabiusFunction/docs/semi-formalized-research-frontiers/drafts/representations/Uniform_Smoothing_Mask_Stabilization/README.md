# Uniform Smoothing and Commensurate Observation Masks

A seven-page mathematical continuation of Universal Comparison of Fabius Observation Masks.

The report proves an exact criterion for finite commensurate masks of unequal cardinalities: the source must have at least as many coordinates as the target, the q-integer denominator must divide the numerator, and an explicitly given signed cardinal spline must be nonnegative. Exponential tilting does not change its sign.

A direct application of classical Polya positivity, using the half-unit digit decomposition of a uniform variable, proves that a finite signed lattice measure becomes nonnegative after sufficiently many unit-uniform convolutions exactly when its polynomial is positive on the positive real axis. Consequently a finite number of additional base-cap source observations permits universal mask domination exactly when the denominator polynomial divides the numerator, equivalently when all nontrivial cyclotomic divisor counts are nonnegative.

For P(u)=1-u+u^2, the least uniform-smoothing order is exactly nine. The report includes all six Bernstein rows needed by symmetry, the negative order-eight value -17/2520, and a separate order-eleven half-step coefficient certificate. Thus nine additional h-cap observations are necessary and sufficient to upgrade source caps (h,6h) to dominate target caps (2h,3h), uniformly over all common real tilts and all total-sum weights.

## Files and reproduction

- uniform_smoothing_mask_stabilization.pdf: complete report
- uniform_smoothing_mask_stabilization.tex: editable source
- build.sh: standard TeX Live build
- SOURCES.md: references and exact repository context
- validation.json: artifact verification and exact-check summary
- checks/verify_stabilization.py: Python standard-library certificate checker
- checks/stabilization_certificates.json: all eleven exact Bernstein rows, the order-eight obstruction, the half-step certificates, and algebraic results
- checks/verification.log: recorded checker output
- SHA256SUMS: integrity manifest

Run `bash build.sh` to rebuild the PDF with standard TeX Live. Run `python3 checks/verify_stabilization.py` for the exact arithmetic checks. These verify the sharp order-nine certificate by two independent Bernstein coefficient computations, reflection and integral one, 1,344 normalized-coefficient identities, and 7,056 polynomial-divisibility cases. The general eventual-positivity proof is analytic. The report describes a terminating algorithm for arbitrary rational data; the included checker verifies its formulas and the displayed example rather than implementing a general-purpose Sturm solver.

## Attribution and scope

Polya's theorem and the eventual positivity of polynomial coefficient measures have classical antecedents, explicitly cited. No general priority claim is made. All comparisons require one observation kernel valid for the entire total-sum weight or threshold family; they do not decide every isolated two-hypothesis comparison. The arguments are ordinary mathematical proofs, not formalized or externally refereed results.
