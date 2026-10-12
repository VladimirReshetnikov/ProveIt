# Reproducing the computational diagnostics

From the package root, run:

```sh
python verification/verify.py
```

The default run writes fresh output to `build/verification/`. It does not
overwrite the delivered numerical data. To regenerate the delivered paths:

```sh
python verification/verify.py --output data --figures figures
```

The calculation used Python 3.12.14 and the versions pinned in
`requirements.txt`. It uses 85 decimal digits by default. Package versions,
working precision, truncation sizes, comparison errors, and normalized root
residuals are included in the JSON output. Other options are `--dps`,
`--plot-T`, and `--no-plots`.

## What is checked

1. Sixteen finite exact symbolic checks compare the Bell-polynomial
   resonant jet formula to a direct CAS Laurent expansion of the Gamma
   function, for orders 1 through 4 and derivatives 0 through 3.
2. Six exact families independently revert generic logarithmic germs with
   every lower analytic and logarithmic coefficient present. They check
   the degree bound and the highest-logarithm Fuss--Catalan coefficients.
3. Twenty-four high-precision comparisons check integer-order polylogarithm
   jets against independent, exponentially convergent defining sums at
   `t=0.25` and `t=0.75`.
4. Nine further defining-sum comparisons check the pole-cancelled critical
   evaluator at `t=0.5`, `epsilon=-0.1,0,0.1`, and weights 0, 1, 2.
5. Twenty-seven inverse cases evaluate the leading term and first
   correction at weights 0, 1, 2, `tau=-2,0,2`, and `T=30,60,120`.
6. A 183-point inverse grid at `T=240` generates the crossover error figure.
7. The pure-dilogarithm Lambert formula is checked symbolically through
   cubic order and numerically at four values of its Lambert parameter.

The symbolic computations are exact **finite** checks. The general
statements are proved in the article. The numerical comparisons are
floating-point diagnostics, not interval enclosures or additional proof
assumptions.

## Reference evaluations and truncation

The moderate-argument reference values use the defining exponential
polylogarithm series. For the ranges used, the absolute weight is at most
one, giving the recorded geometric bound on the omitted series tail.
This is an analytic truncation bound; numerical summation and evaluation
are still floating-point operations.

The small-argument inverse evaluations solve the normalized variable
`v`, using the pole-cancelled Jonquiere normal form. Their regular power
series retains the recorded number of terms. Thus the reported residuals
refer to that computed equation. The independent moderate-argument
comparisons check the normalization, derivative signs, and implementation.
No claim of interval-certified inversion is made.

Preparatory diagnostics found inconsistent results from direct numerical
order differentiation of `mpmath.polylog` at an integer order. The delivered
script therefore uses independent convergent defining sums as its
order-derivative reference.

## Reading the approximation data

`critical_inverse.csv` records **signed** relative errors. In the requested
moderate-`T` sample, adding the first correction does not always improve
accuracy and can produce a nonpositive truncated approximation. Such a
row is retained and explicitly flagged; it is not a failed inverse solve.
The theorem is an asymptotic statement for sufficiently large `T` and an
exact convergent analytic representation. It does not guarantee that its
first two terms are positive or accurate for every finite `T`.

The figure uses `T=240` to show the later asymptotic regime over
`tau in [-3,3]`. Its vertical axis is the absolute relative error. The full
data, including the earlier problematic truncations, remain in the CSV and
JSON files.

The same records also generate `verification_table.tex`, a concise
coverage-and-error summary, and `crossover_table.tex`, a signed relative
error table at `T=60` and `T=120`. Regeneration does not require hand-copying
numbers into the article.

## Ordinary inverse coefficients

Run the separate coefficient program from the package root:

```sh
python verification/coefficients.py
```

It writes to `build/verification/` by default; use `--output data` to regenerate
the shipped coefficient files and `coefficient_table.tex`.

The program checks exact rational composition through degree 12 for the
inverse functions of orders 2, 3, and 4. It checks the first four
reciprocal-Gamma coefficient formulas symbolically and compares the first
seven numerically with an independent Gamma-derivative formula. Six finite
inverse Taylor coefficients, at indices 96 and 256 for those three orders,
are evaluated at two precisions, with 60 additional digits in the second
calculation. The greatest working precision is 376 decimal digits; the
maximum observed relative discrepancy is below `3.09e-129`.

For the dilogarithm, the program also evaluates the exact upper-bank
dilogarithm by its reflection formula and integrates the localized scaled
cut up to `v=120` and `v=180`. It records the difference between those
cutoffs, the difference from finite Lagrange coefficients where available,
and several truncations of the all-orders Lambert expansion. The coefficient
indices are 96, 256, 10^6, 10^12, and 10^30. At the two smaller indices the
local-cut agreement with the finite coefficient is approximately 3.36e-19
and 3.62e-26 in the stated normalization. The cutoff difference is separately
reported and must not be mistaken for a bound on the omitted outer contour.

Every cut integral in the program has a **finite** upper limit. In particular,
the code does not integrate the formal factor `exp(-v+v*log(v)/H)` to infinity
at fixed H; that improper integral need not converge. The proof in the
article explains the cutoff and fixed-order coefficient integration.
