# Reproducibility checks

Run with Python 3.10 or newer and `mpmath==1.3.0`:

```sh
python3 -m pip install -r scripts/requirements.txt
python3 scripts/replay.py
```

Run from the report directory, or supply the script's path from any other
working directory. All generated files go in `results/` relative to the script;
no network access or external input files are used during replay. The script
does not modify the report's TeX. Outputs have no timestamps or random inputs.
One complete replay took about 7.3 seconds with Python 3.12.14 and mpmath 1.3.0
in the preparation environment; runtime depends on the machine.

## What is exact

- `exact_algebra.py` implements finite formal polynomial arithmetic over Python
  `fractions.Fraction`. The pure Gaussian construction and the transformed
  third-order recurrence give identical `d0,...,d12`.
- The transformed recurrence operator's vanishing low degrees and its
  `-4k` diagonal coefficient are checked exactly for `k=0,...,12`.
- The Bernoulli-polynomial generator computes `c0,...,c8`. The independent mixed
  Gaussian transform is evaluated through `t16`: its even coefficients match
  all nine `c` coefficients and every odd coefficient vanishes. This includes
  the originally requested check through `t8`.
- The original integer sequence's recurrence matches its defining finite sum
  for `n=0,...,30`, is integral through `n=1000`, and satisfies
  `a_n >= n*a_(n-1)` on `n=2,...,1000`.

## What is numerical

- The normalized recurrence is rerun from scratch at 200 and 300 working
  decimal digits through index 100. Their scaled differences are asserted
  smaller than `1e-170`; the 300-digit run is compared with the exact first
  thirteen coefficients. Both runs are saved at 180 significant digits.
- Ratios and first-four-term residuals are printed at indices 20,40,60,80,100.
  The residual divided by the next Gamma scale is also recorded. These checks
  do not by themselves prove the all-orders late expansion.
- The original Lambert-W continuous inverse is evaluated at six exact sequence
  values. The integer-threshold inverse retains its separate rounding issue.
- The late inverse comparison evaluates the first Lambert-W correction and
  numerically solves a four-term late-asymptotic model. A model root is neither
  an exact continuous interpolation of the discrete coefficients nor a proof
  of inverse error estimates or all-index monotonicity.

All floating-point evidence is **non-certified**. Agreement at two precisions
is a reproducibility/consistency test, not interval arithmetic or a rigorous
forward-error certificate. The finite computations do not replace the analytic proof in the article.

## Outputs

- `exact_coefficients.json`
- `high_precision.json`
- `original_sequence_and_inverse.json`
- `late_inverse_models.json`
- `numerical_tables.tex` (optional compact tables, not included automatically)

The implementation is original finite algebra based on the formulas stated in
the report. No third-party source code or private working notes are packaged.
