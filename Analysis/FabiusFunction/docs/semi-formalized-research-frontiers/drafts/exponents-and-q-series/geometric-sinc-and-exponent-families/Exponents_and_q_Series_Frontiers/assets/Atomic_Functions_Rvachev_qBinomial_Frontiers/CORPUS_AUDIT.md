# ProveIt Fabius/Rvachev corpus audit

## Boundary

The atomic-function audit is pinned to repository commit
`c853d2e8fb9b326742339c7672fe0e130211873a`, the first repository head after the
revised `Atomic_Functions_Rvachev_Report` package was merged into the consolidated
exponent-and-q-series frontier volume. The repository was then compared through
`185550b752f44720d89e28c38784e61ca69487bb`.

GitHub code search reported 79 `*.tex` paths below
`Analysis/FabiusFunction/docs`. The raw count includes canonical expositions,
consolidated frontier volumes, deliberately independent Fourier-decay witnesses,
vendored papers, and historical source assets retained after editorial merges. The
repository `MANIFEST.md` and group README files were therefore used to interpret the
inventory rather than treating every path as an independent theorem source.

The seven commits after the atomic pin changed the Lambert-W consolidation, transform
formalization, and manifests. They did not alter the atomic derivative geometry used in
the report's nonduplication claims.

## Results already present at the pin

The current corpus already contains, among much else:

- the translated/reconstructed general atomic-function chapter and the family
  `h_a` with its infinite sinc product;
- Bernoulli cumulants, Bell-polynomial moments, and q-Pochhammer denominator
  structure;
- the exact Cantor nonanalyticity set for `a > 2`, gap degrees, signed leading
  coefficients, fractal-string/tube formulae, and the geometric local-degree law;
- derivative equimeasurability, exact rearrangements and `L^p` norms;
- the q-Gaussian parity-tower Gram kernel `q^((j-k)^2)`, principal Gram
  determinants, pivots, and Jacobi-theta Riesz bounds;
- log-Weibull intermittency for the local leading coefficient;
- the generalized `Fup_n` hierarchy, cumulants, CLT, and the uniform
  all-orders differentiated Edgeworth theorem;
- the general-base negative-Laplace/Gamma-zeta periodic correction, the
  Stieltjes-Wigert spectral bridge, and the Mellin law of distance to `K_a`;
- the broader Thue-Morse, q-binomial/Richardson, inverse-Fabius/Lambert-W,
  integral-transform, dyadic-comb, and representation corpora.

These are marked as current-corpus or inherited results in the report, not claimed as
new.

## Targeted nonduplication searches for this revision

The following formula/title/keyword families were searched across the TeX corpus:

1. **Explicit orthogonalization**
   - `Gaussian binomial` + `derivative Gram`
   - `q-binomial` + `Gram-Schmidt`
   - `q-Vandermonde` + `parity tower`
   - exact patterns corresponding to `q^((j-k)^2)` and the proposed triangular
     coefficients

2. **Finite matrix factorization and inverse**
   - `Cholesky` + `q-binomial`
   - `checkerboard inverse` + `derivative`
   - the product/generating-function pattern `(-q z; q^2)_infinity`

3. **Arbitrary minors**
   - `Schur minor`
   - `generalized Vandermonde` + `Gaussian Gram`
   - `strictly totally positive` + `derivative tower`

4. **Prediction/spectral factorization**
   - `theta whitening`
   - `innovation filter`
   - `minimum phase` + `q-Gaussian`

5. **Highest local jet and partial theta**
   - `highest nonzero derivative`
   - `partial theta` + `jet`
   - `jet-distance Mellin`
   - `reciprocal jet moment`

No equivalent corpus statement or formula was located for the new theorem cluster.
This is a corpus-relative conclusion, not a claim of worldwide priority.

## External literature cross-check

Classical Gaussian Toeplitz matrices already have analytic factorization and inversion
literature, notably:

- M. J. C. Gover, *Properties of the Inverse of the Gaussian Matrix*, SIAM J.
  Matrix Anal. Appl. 12 (1991), 541-548.
- J. Pasupathy and R. A. Damodar, *The Gaussian Toeplitz Matrix*, Linear Algebra
  Appl. 171 (1992), 133-147.

Strict total positivity, oscillatory matrices, checkerboard inverses, and
variation-diminishing consequences are classical subjects treated by Karlin and Pinkus.
The report therefore claims only the new identification and deductions within the
Fabius/Rvachev corpus: the explicit Gaussian-binomial derivative transforms, the Schur
minor formula in that setting, the theta-whitening interpretation, and the joint
highest-jet/distance partial-theta transform.
