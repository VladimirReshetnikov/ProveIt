COMPLEX COTANGENT POWERS -- PORTABLE NUMERICAL VERIFICATION

Contents
  verify_complex_powers.py
  complex_powers_verification.json
  requirements.txt

Requirements
  Python 3 and mpmath 1.3.0. No repository checkout, network access, external
  data, compiled extension, or absolute workspace path is required.

Run
  python -m pip install -r PATH/TO/THIS/DIRECTORY/requirements.txt
  python PATH/TO/THIS/DIRECTORY/verify_complex_powers.py

The working directory may be anywhere. The program writes its result beside
the script, replacing complex_powers_verification.json. Run a copy if the
included record is to be preserved unchanged.

Recorded run
  Python 3.12.14; mpmath 1.3.0; 65 decimal working digits.
  16 comparisons; maximum scaled residual 4.4180259e-50.
  Runtime in the recorded environment: approximately 42 seconds.

What is compared
  1. Three nonintegral complex-power Hurwitz generators: direct x-integrals
     against independently evaluated Mellin integrals, using both z
     half-planes and argument-derivative orders zero, one, and two.
  2. Eight special-point Gamma/generalized-harmonic formulas against Mellin
     quadrature at positive integral spectral orders.
  3. Two first exponent derivatives against polylogarithm-zeta differences.
  4. A direct x finite part at lambda=1,p=2 against its finite Fourier formula.
  5. The lambda Laurent constant at that point from eight symmetric pairs
     of nearby exponent values, with Richardson extrapolation.
  6. The difference of those two constants against the correction 2*pi*i.

The nearby-exponent calculation uses a local x-Taylor subtraction followed
by direct polygamma quadrature. It does not insert the predicted correction
or use the generalized binomial-polylogarithm generator.

These are numerical diagnostics. They are not interval certificates and do
not replace the analytic Fourier, Mellin-continuation, and local-amplitude
proofs in the accompanying article. The JSON contains all compared values,
parameters, residuals, and extrapolation samples.
