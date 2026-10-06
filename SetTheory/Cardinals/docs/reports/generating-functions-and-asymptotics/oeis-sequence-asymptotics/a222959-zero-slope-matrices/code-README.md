# Exact arithmetic code

All mandatory code uses only integers, `fractions.Fraction`, and other standard-library modules. It does not use floating arithmetic, fitted coefficients, a computer algebra system, network access, or assertions that disappear under `python -O`.

`matrix_exact.py` implements:

1. Primitive centered weights and complete binary row alphabets
2. Fraction Gaussian elimination for alphabet rank through n=14
3. Bareiss integer elimination for the reduced Gram determinant S^(2n-2)
4. Integer preimages of every reduced-margin basis vector, verifying an integer right inverse and hence saturation at each checked dimension
5. Full projector numerator matrices for n=2,...,12, with exact symmetry, idempotence and trace checks; direct sums for A, B, sum h^2 and sum h^3; independent rational power-sum formulas
6. The exact first-coefficient arithmetic giving exp(-7/5) and c1=171/350
7. Positive/negative-row meet-in-the-middle counts through n=8 by no-carry integer lanes; a separately implemented unpacked tuple count through n=7

For every lane the maximum possible sum is the sum of positive weights, strictly smaller than the chosen power-of-two radix. Python integers are unbounded. Thus integer packing introduces neither lane carries nor machine-word overflow. Squared multiplicities match the two symmetric nonzero-weight row families, and an odd-dimensional zero-weight row supplies one independent row-alphabet factor.

`check_exact.py` compares these computations with the fixed reference fixture and additionally checks the Bernoulli truncated-gauge Rayleigh quotient S/[4(2S-1)] and records the corresponding half-covariance quadratic-form quotient S/[8(2S-1)]. It writes only to an explicitly new output outside the package. The optional `--max-n9` flag enumerates 7,311,616 tuples and can require substantially more memory and time; it is not used by the builder or standard replay.

The finite checks corroborate algebra and small enumerations. They do not prove uniform analytic remainders, localization for all dimensions, eventual positivity, or all-orders coefficient transfer. Those claims require the manuscript's analytic proof. No c_j with j>=3 is claimed by this code.

## Second correction

`derive_second_correction.py` enumerates connected degree multigraphs for covariance(Q4,Q6) and the third cumulant of Q4. It expands each projector edge into three tensor terms, contracts equality blocks, and collects exact power-sum monomials. This produces finite exact formulas, not a fit or interpolation. It extracts leading coefficients using s_r=n^(1-r)(3^r/(2r+1)+O(n^-2)), with the lower-moment contributions shown in the manuscript.

`verify_second_correction.py` checks the collected polynomials against separately transcribed formulas and recomputes Gaussian raw moments by an integer Wick recursion at n=2,...,5. It compares quartic variance, covariance(Q4,Q6), the third quartic cumulant, and lower moment formulas. The graph contraction and raw-moment recurrence are different computational routes; both use the same explicitly stated projector covariance.

The mandatory replay records both complete polynomial derivations and raw-moment verification, including c2=483051/245000, the normalized logarithmic coefficient 6483/3500, and phase r2=2983/3500. The two modules are side-effect-free libraries invoked by `check_exact.py`. They implement these particular finite contractions, not a general all-orders engine. The justified analytic remainder and power-counting arguments remain in the manuscript.
