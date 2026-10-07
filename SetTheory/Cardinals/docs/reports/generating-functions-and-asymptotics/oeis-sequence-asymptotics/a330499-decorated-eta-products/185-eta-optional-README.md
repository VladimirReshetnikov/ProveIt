# Optional numerical diagnostics

These programs accompany Report185 on A330499. They are separate from the
standard-library-only mandatory exact checks. They use finite-precision arithmetic
and finite mode sums. Their `PASS` means only that the displayed finite regression
guards passed. It is not a proof, interval enclosure, uniform asymptotic error
certificate, or certified integer-inverse threshold.

## Running

Run from the package root, with Python 3.12 (the tested version). The tested optional
stack is pinned in `optional/requirements.txt`. Only the precision, Laguerre and
inverse programs require `mpmath`. Only the FFT and two-point programs require
`numpy` and `scipy`; the FFT's exact-input overlap uses Python's `decimal` module.
The combined entry point needs all three packages. There is no network access in
these programs.

```sh
python -B optional/diagnostics.py
python -B optional/laguerre_check.py
python -B optional/check_two_point_decoration.py
python -B optional/fft_experiment.py
python -B optional/inverse_experiment.py
python -B optional/run_all.py --output /your/new/output.json
```

Each command writes JSON to stdout unless `--output NEW_FILE` is supplied. An
output file must not already exist; its parent directory must exist. Existing
receipts, source files and inputs are never overwritten. All programs have main
guards, explicit failure checks and no assertion-dependent checks. `python -O -B`
keeps the checks enabled. Importing a program does not run its experiment.

Exact coefficient inputs normally come from `code/verify_exact.py:exact_values`.
If that file is absent, the scripts use the disclosed self-contained integer
recurrence in `_common.py`; `--standalone` explicitly selects that route. The
receipt records `exact_input_engine`. The fallback is a repeated implementation
of the same recurrence, not an independent mathematical certificate. The optional
programs do not change the mandatory exact check's bounds.

`optional/receipts/all_optional.json` is a precomputed combined receipt generated
by the default commands. Running `run_all.py` creates a fresh computation; it does
not read or pass tests by trusting the saved receipt. `data/diagnostic_provenance.json`
records adaptation and receipt digests, the tested stack, checks against the frozen
numerical evidence, and replay checks. No historical source files are included in
this optional directory.

## Five computational routes

Let `E(n) = n^(3/4) (a(n) rho^n/n! - C)`. In the JSON, `Hj` means the report's
`H_j(sqrt(n))`; the shared `_mp.harmonics(x)` accepts `x`, not `sqrt(x)`.

1. **Precision replay (`diagnostics.py`).** The exact integer recurrence supplies
   `a(n)`. Each sample is recomputed at 50 and 80 decimal digits with 30 eta modes.
   It compares the scaled coefficient error, all three harmonic terms, the scaled
   three-term residual, core/shifted/three-term inverse errors and root-equation
   residuals. Every field is compared at high precision before decimal display.
   Default samples: 100, 200, 400, 600. Each absolute precision discrepancy must
   be less than `1e-35`; the absolute residual
   `n^(3/2) (E(n)-H0-H1/sqrt(n)-H2/n)` must be less than 1.

2. **Laguerre finite jet (`laguerre_check.py`).** An independent associated-Laguerre
   three-term recurrence computes `L_n^(-j-1)(A)`, using the identity
   `[x^n](1-x)^j exp(-A/(1-x)) = exp(-A) L_n^(-j-1)(A)`.
   The analytic decoration jet is retained through degrees 0, 1, 2 and 3, using
   11 modes at 60 digits. This route does not call the harmonic correction formula.
   Default samples: 50, 100, 200, 400, 800, 1000, 2000. Each absolute scaled error
   must be less than 0.1; the degree-three error must be less than 0.01 below 100
   and 0.001 from 100 onward. These deliberately finite tolerances accommodate
   the visibly non-monotone small-n behavior; no monotonic improvement in jet
   degree is claimed.

3. **Two-point decoration (`check_two_point_decoration.py`).** For
   `B(z)=(z+z^2)/2`, coefficients are evaluated independently as
   `sum_{k=ceil(n/2)}^n c_k binom(k,n-k)/2^k` using log-gamma and binary64.
   The universal H0/H1 formulas use `mu=3/2`, `v=1/4`, `kappa3=0`,
   `d=1/18`, `q=-1/216`, and 99 modes. Default samples:
   100, 300, 1000, 3000, 10000, 20000. The absolute residual after H0/H1,
   multiplied by `n^(7/4)`, must be less than 1.

4. **FFT extraction (`fft_experiment.py`).** An independent route extracts
   coefficients from the eta-transformed generating function, with the pole
   subtracted, on a circle of radius `exp(-40/N)`. Defaults: `N=262144`, 80 eta
   modes, binary64 arithmetic, indices through 64000. The H1 comparison uses the
   alternate D(A) form of the first-correction formula and 19 harmonic modes.
   It checks positive `Re(1/t)`, imaginary leakage below `1e-10`, exact-integer
   overlap of scaled errors through 2000 below `1e-7`, and absolute
   `n (E(n)-H0-H1/sqrt(n))` below 1. `--points 524288` gives a doubled-grid
   diagnostic. Neither grid size encloses aliasing, finite-radius, truncation or
   roundoff error.

5. **Smooth inverse (`inverse_experiment.py`).** At targets `Y=a(n)`, 60-digit
   root finding compares the exact factorial core, its first oscillatory shift,
   and the chosen three-term amplitude model with `n`, using 19 modes. Default
   samples: 100, 200, 400, 800, 1000, 2000. Absolute core and shifted errors must
   be below 0.001; three-term model errors below 0.00001; root-equation residuals
   below `1e-40`; and the three-term scaled coefficient residual below 1.
   A small continuous-root error cannot justify taking its ceiling uniformly
   near integer jumps. The integer sequence has no canonical real interpolation.

The bounds above are regression thresholds chosen for these bounded computations,
not asserted asymptotic constants. Scripts disclose their finite ranges and reject
parameters outside them. Successful 50/80 agreement can still share systematic
formula, truncation or conditioning error. The report's proof is separate.

## JSON schema (version 1)

Every result has `schema_version`, `status`, `diagnostic`, `boundary`, and either
`rows` or `receipts`. Individual receipts also contain numerical parameters,
`versions`, and explicit `checks` thresholds. `status` is `PASS` only after every
check completes; a failed guard exits nonzero and emits no successful receipt.

- The precision receipt's rows contain `n`, `dps_50`, `dps_80`, and
  `maximum_absolute_precision_delta`. The two precision objects use identical
  field names. Arbitrary-precision values are decimal strings (40 significant
  digits), avoiding JSON binary64 conversion.
- Laguerre rows contain `n`, `scaled_error`, and four-element
  `predictions_J0_to_J3` and `errors_J0_to_J3` decimal-string arrays.
- Two-point rows contain `n`, `coefficient`, `H0`, `H1`,
  `after_H0_times_n_5_over_4`, and `after_H0_H1_times_n_7_over_4` as JSON numbers.
- FFT rows contain `n`, `scaled_error`, `H0`, `H0_H1`, and `after_H1_times_n`.
  Rows through 2000 additionally contain `exact_input_scaled_error` and
  `absolute_overlap_error`. Values are JSON numbers.
- Inverse rows contain `n`, three named inverse errors, two log-equation residuals,
  and `three_term_scaled_residual`, with numerical values as decimal strings.
- `run_all.py` wraps all five receipts under their diagnostic names in `receipts`.
  No timestamps or machine-specific paths enter these deterministic receipts.

Normal and optimized runs are expected to be byte-identical on the same installed
stack. Different numerical library versions, architectures or FFT implementations
may differ in trailing digits; passing the disclosed finite tolerances is the
portable numerical expectation, not cross-platform byte identity.

## Historical numerical outputs

`historical/` preserves five original numerical output files byte-for-byte:
`explore.json` (exact-input logarithms and selected scaled errors through 2000),
`inverse_experiment.json` (smooth-model comparisons), `fft_experiment.json`
(the original 262144-point extraction through 64000),
`check_two_point_decoration.txt` (the original two-point finite-sum output through
20000), and `replay.json` (the original exact/50-and-80-digit replay receipt).
They are historical diagnostics, not certificates. The portable scripts above
recompute their routes and produce the newer, more explicit receipt schema.
Numerical comparisons and file hashes are recorded in
`data/diagnostic_provenance.json`. Original environment-specific scripts, research
notes and third-party source records are excluded.
