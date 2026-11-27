# Internal proof review

The two mathematical arguments were developed on separate tracks and checked again by another reasoning pass. This record is an internal analytical check, not external peer review or a Lean proof certificate.

## Prime-counting result

The review checked the sinc-squared majorant and Fourier support, convolution exponents in the local L4 estimate, zero-series tail rates, distributional identification, the prime-square and central-zero terms, the exact partial-summation endpoint, the Volterra remainder, uniformity over interval origins and directions, grouped coincident zeros, arbitrary real prime-probe shifts, the covariance lower bound, the occupation inequalities, and finite-frequency prediction. No substantive mathematical defect was found.

Banks, arXiv:2302.07073v2, Theorem 1.2 was checked directly in the primary PDF. For each fixed argument u>2 its error is O(log T); the distance to other prime powers is fixed and positive. The classical zeta version covers the conductor-one character. This supports the normalization used in the paper.

## Symplectic result

The independent derivation checked the orbit count, affine fibre, isotropic kernel probability, exact rank sign threshold, boundary coefficient, uniform rank asymptotic, chi-square tail estimate, and lower and upper testing bounds, including the endpoint n=c. Detailed algebra is in INDEPENDENT_MATH_REVIEW.md.

The packaged verification program was also rerun by the integrating process: 313,170 frames and 11,295 matrices passed the exhaustive checks; 288 rational formula cases passed. These finite checks do not constitute a proof for all parameters.
