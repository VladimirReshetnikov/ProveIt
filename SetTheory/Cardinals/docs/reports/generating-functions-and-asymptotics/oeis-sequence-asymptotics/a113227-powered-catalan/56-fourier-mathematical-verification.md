# Mathematical verification of the Fourier sector addendum

Reviewed 1 October 2026.

## Verdict and review scope

PASS: no unresolved mathematical gap found in the stated fixed-sector theorem.

The positive-spectrum and real all-orders input had already received independent audit in the companion report. The two new components were developed separately and then independently cross-reviewed: the complex Bessel wedge lemma was checked separately from its derivation, and the spectral-replacement/Fourier/saddle argument was checked separately from its derivation. A further integrated review checked the combined argument. This is component cross-review plus integrated mathematical review, not formal verification or conventional peer review.

Final reviewed editable source: powered-catalan-fourier-addendum.tex

SHA-256: 801866eeb7969e514be4ebbc271c4136ae0f4e9181d2be51be38e064ba3ff175

## Checks of the complex Bessel component

- The Schlaefli integral has the correct sign, powers, and adjacent-order difference
- The auxiliary Bessel terms and small contour-rotation arc are negligible relative to the Gamma term uniformly in each fixed wedge
- Rotation through the complex Gamma saddle avoids an exponentially bad absolute-integral estimate
- The singular untruncated exponential is never extended to zero; only its finite polynomial truncation is extended
- The finite Gamma identities give the stated reciprocal products with the correct normalization
- Cauchy product remainders are polynomial in the summation index and summable against 1/j!
- Eventual zero-freeness follows from the normalized 1+O(1/|z|) estimate
- Derivative bounds apply to analytic normalized remainders on a larger wedge and do not differentiate the nonanalytic auxiliary cutoff

## Checks of spectral replacement and Fourier sectors

- Splitting the full spectrum at sqrt(n) makes the node displacement estimate uniform while lower nodes are superexponentially negligible
- The modified Bell saddle has loss n log(1+c)+O(n/log n), proving every d<log 2 globally
- The chosen real cutoff rates exceed log 2, including half-integer rounding errors
- Poisson summation is used for the paired real series; its first boundary term is purely imaginary
- The rectangle orientation is correct and real pairing produces the necessary O(y) factor at each vertical endpoint
- The infinite vertical sum is controlled by the integrable kernel y exp(−2 pi m y)/(1−exp(−2 pi y))
- A common horizontal height controls all omitted modes by a geometric sum, while the phase has a unique global maximum on the full window
- Lambert branch indexing gives upper-half-plane saddles for positive Fourier modes
- The fixed-order Gaussian remainder is uniform despite growing w; the exact real coefficient generator continues to each complex saddle
- The first two rational correction functions were independently reproduced by finite Gaussian expansion
- The envelope derivative calculation has the stated sign, coefficient, and error scale

## Limits retained in the report

- The number of modes and algebraic order are fixed
- Exact cutoff-defined sectors are distinguished from their finite asymptotic expansions
- Oscillatory real pairs have absolute envelope errors, not relative errors near their zeros
- No canonical Borel summation, growing-mode theorem, or infinite sector expansion is claimed
- No exponentially accurate inverse is inferred from a finite principal algebraic expansion
- Numerical tests are diagnostics, not interval certificates or proof-assistant certificates
- No comprehensive priority or nonduplication claim is made

Conventional specialist peer review remains appropriate before publication.
