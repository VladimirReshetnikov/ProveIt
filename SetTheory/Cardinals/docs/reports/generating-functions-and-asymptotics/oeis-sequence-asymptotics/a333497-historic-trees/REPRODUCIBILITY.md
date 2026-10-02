# Computational reproducibility

This directory contains a curated copy of the original computational evidence for
A333497, the order-4 (m=3) extension, and the order-30 (m=29)
obstruction and uniform extension to every m >= 29, with replayable source. It contains no working notes or third-party papers.
Exact arithmetic checks and floating-point experiments are explicitly separated.
The current final verification snapshot is `data/verified_final_replay.json`.
A successful replay is a computational regression check, not a substitute for
proof of the report's analytic assertions.

## Quick replay

With Python 3.12 and the packages in `requirements.txt` available:

```sh
./replay.sh
```

The checked environment used Python 3.12.14, mpmath 1.3.0, SymPy 1.14.0,
NumPy 2.3.5, and SciPy 1.17.0. The requirements file pins those package versions;
the scripts do not install software or make network requests. `PYTHON` may select
a different interpreter, for example `PYTHON=python3.12 ./replay.sh`.

Every run creates a fresh `historic-tree-replay.*` directory under `${TMPDIR:-/tmp}`,
prints its path, and leaves it available for inspection. Shipped data are never
used as an output directory. Replay verifies their hashes before and after the
run. The driver first verifies the bundled computational scripts and reference
artifacts against their provenance hashes. There is no automatic cleanup,
including on failure.

The output tree contains:

- `producer/`: freshly recomputed exact data, symbolic checks, two high-precision
  fits, and inverse experiments
- `independent/`: freshly recomputed exact counts through index 600 and the
  independent symbolic/ODE checks
- `extensions/`: exact order-4 algebra/counts and original exact stability and
  order-30 obstruction certificates
- `logs/`: complete stdout/stderr for each stage
- `environment.json`: interpreter, platform, machine, and package versions
- `replay_summary.json`: stage arguments, exit codes, times, exact and floating
  comparison results, and overall status

For an explicit empty output directory outside the release tree:

```sh
python3 code/run_replay.py --output-dir /tmp/my-empty-historic-tree-replay
```

The driver rejects a nonempty output directory and any output path inside the
release tree. Run the scripts through this driver or `replay.sh`: individual
original scripts retain their historical default of writing beside themselves.
Their path overrides are described below.

## Calculations replayed

1. `verify_symbolics.py`: exact SymPy verification of the stated Lyapunov and
   energy identities, indicial factorization, conjugacy of formal coefficients,
   and `a11 = -1/7`. It generates exact integer counts for indices 0–202 and
   checks them against the rational ordinary-EGF recurrence through index 72.
2. `numerical_expansion.py`: scaled coefficient recurrence through index 1000;
   a degree-4 fit for `rho`, `Re(C)`, and `Im(C)` at 120 decimal working precision
   with training indices 400, 550, 700; then at 150 decimal working precision with
   training indices 450, 650, 850. Formal coefficients are generated through total
   degree 6, and reported residuals use degrees 1–5. The scripts' rows include
   both training and non-training indices; not every row is a held-out check.
3. `verify_inverse.py`: 100-decimal-working-precision inverse experiments using
   the newly generated 150-digit fit and exact counts. Thresholds at indices
   75, 100, 150, 200 and geometric midpoints are checked. The midpoint ceiling
   checks do not assert an unconditional ceiling rule at arbitrary thresholds.
4. `independent_checks.py`: a separately implemented exact integer recurrence
   through index 600, an independent rational EGF recurrence through index 80,
   exact symbolic checks, and an independent double-precision DOP853 ODE run.
   The ODE uses time interval `[0,100]`, `rtol=2e-13`, `atol=2e-14`, and a terminal
   tail estimate `3*v(100)/p_star`. The independent residual calculation then uses
   the newly generated 150-digit fitted constants against independent exact
   counts; those residuals are not independent fits.
5. `extensions/verify_stability.py`: the original exact, integer-rescaled Routh
   certificates for orders 2–40; independent exact complex Cauchy-index counts
   for orders 29 and 30; imaginary-axis exclusions and simple-root checks at
   those two orders; the order-3 additive-compound graph at order 30; and exact
   rational phase/modulus inequalities for orders 30–37 with test value 228/25.
6. `extensions/verify_audit.py`: the original independently constructed
   order-30 certificate, using unscaled rational Routh rows. It certifies three
   right-half-plane and 27 left-half-plane roots of the full polynomial, checks
   simplicity and absence of imaginary roots, and checks all 11,340 exterior
   signs plus forward/reverse reachability of all 4,060 compound vertices.
7. `extensions/verify_r4_checks.py`: a new exact supplement checking the
   normalized order-4 equilibrium and Jacobian spectrum; the characteristic and
   indicial factorizations; the energy derivative and value 1/6 at the all-one
   initial jet; the pure real-mode coefficient `D = -1/18052070400`; its strictly
   alternating mode vector; universal leading factorial normalization and the
   order-4 prefactor 140; and integer/rational EGF recurrences through index 100.
   These are finite algebraic checks, not mechanical proofs of complex
   continuation, amplitude nonvanishing, or the obstruction theorem.
8. `extensions/verify_phase.py`: the original independent pure-standard-library
   verifier recomputes all eight finite-bridge phase/modulus margins as exact
   fractions, compares them to the freshly generated producer certificate and a
   second original exact reference, and checks strict margins greater than
   1/200 and 1/1000. Its printed decimal minima are orientation only; the
   assertions and JSON certificate use exact fractions.
9. `extensions/verify_uniform_constants.py`: a new pure-standard-library check
   of the rational constants at the infinite-range threshold r=38. It verifies
   `56/81 - 76/111 = 20/2997 > 0` and
   `753140/110889 - 44/7 = 392864/776223 > 0`, as well as the rational
   expressions producing the two threshold bounds. Their extension to every
   r >= 38 uses the analytic inequalities and monotonicity proved in the report.

For reference, the exact recurrence is
`h[n+3] = sum(binomial(n,k)*h[k]*h[n-k], k=0..n)` with `h[0]=h[1]=h[2]=1`.
The ordinary-EGF recurrence divides the corresponding convolution by
`(n+1)*(n+2)*(n+3)`, starting from `1,1,1/2`.

## What is verified

The following newly generated artifacts are compared to the original reference
bytes using SHA-256; JSON artifacts are additionally compared as parsed JSON:

- `data/producer/exact_values_0_202.json`
- `data/producer/symbolic_validation.json`
- `data/independent/exact_h_0_600.txt`
- `data/extensions/routh_certificates_2_40.json`
- `data/extensions/independent_complex_root_counts.json`
- `data/extensions/compound_graph_certificate.json`
- `data/extensions/certificate.json`
- `data/extensions/r4_exact_certificate.json`
- `data/extensions/exact_h_r4_0_100.json`
- `data/extensions/rational_phase_certificates_30_37.json`
- `data/extensions/phase_certificate.json`
- `data/extensions/uniform_threshold_certificate.json`

The second original finite-phase reference, `data/extensions/phase_finite.json`,
is not overwritten or regenerated: the independent phase stage recomputes its
rational values and checks equality against it entry by entry. Its original
bytes are additionally checked against the provenance hash.

The exact fields of the mixed independent-check JSON are compared separately.
The exact 0–600 count file's SHA-256 is
`aa02b70dab0ee9522c1a5dea137dd6cd2158b0401671e85da9db160d774bf635`.

All four floating/mixed JSON outputs are also compared byte-for-byte and as
parsed JSON. Equality is a reproducibility observation only. A platform or
library change may alter floating output. Such differences are prominently
recorded as warnings, rather than being mistaken for a proof failure.

The driver returns a nonzero exit status for an execution failure, exact-data or
exact-field mismatch, a failed exact boolean check, an unsuccessful ODE solver,
a failed inverse midpoint check, or any modification to shipped data. Floating
JSON inequality alone is a warning, since the computations are non-certified.
Consult `floating_outputs_identical_to_reference` as well as `overall_pass`.

The original order-3 checked run is preserved in `data/verified_replay.json`.
The intermediate order-4/order-30 run is preserved in
`data/verified_extension_replay.json`. The current complete run, including the
uniform extension, is `data/verified_final_replay.json`.
Each snapshot records the actual script hashes and environment for that run;
older snapshots intentionally predate later script additions. They are
not a promise of identical floating results on every platform. Stage log paths
refer to that run's temporary output; logs are produced anew rather than shipped.

## Numerical limits

The fitted constants, all decimal residuals, and the ODE estimate are
**exploratory and not interval-certified**. Decimal working precision is not a
claim that that many digits of a fitted constant are correct. Fitting a truncated
expansion leaves truncation/model error. Agreement between fits at different
precisions/training indices is evidence of stability, not a rigorous bound.
The ODE's success status and tolerances do not certify a global error bound or
the terminal-tail approximation. Exact symbolic identities and recurrences do
not by themselves certify the report's complex-analytic or transfer hypotheses.

## Source preservation and adaptations

`data/provenance.json` records original and bundled SHA-256 hashes of the seven
original computational scripts and the original hashes of every original
reference artifact. The seven original order-3 reference files and seven original
extension reference certificates were copied byte-for-byte. The new order-4
supplement and uniform-threshold source, with their three output files, are
explicitly distinguished from original artifacts in that provenance record.
The historical hash of the earlier stability-script snapshot is retained too. The 100-digit exploratory producer run
and duplicate console logs were omitted because the requested replay uses the
120- and 150-digit runs; each replay generates fresh console logs instead.

The seven copied computational scripts preserve the original mathematical logic.
The only adaptations are:

- Add the standard-library `os` import and route output through
  `HISTORIC_TREE_OUTPUT_DIR` when set
- For inverse and independent checks, route producer input through
  `HISTORIC_TREE_INPUT_DIR` when set; the independent script's original
  `originals/numerics_150dps.json` input becomes `I/numerics_150dps.json`
- For the independent phase verifier, replace its machine-specific absolute
  paths with `HISTORIC_TREE_INPUT_DIR` for the freshly generated phase data and
  `HISTORIC_TREE_REFERENCE_DIR` for the shipped second exact reference
- Neutralize one incidental comment in the symbolic script without changing the
  energy identity

`code/run_replay.py` and `replay.sh` are new orchestration code.
`code/extensions/verify_r4_checks.py` and
`code/extensions/verify_uniform_constants.py` are new exact verification code. No recurrence,
formal coefficient formula, fitting equation, precision setting, index range,
solver method, solver tolerance, inverse equation, or reported numerical value
was changed in the copied computational scripts.


## Extension scope and exclusions

The stability table spans orders 2–40 because that is the original exact
certificate's range. The table alone does not establish behavior of any
specified nonlinear orbit, and it does not establish that order 30 is the first
failure of the coefficient conjecture. The order-30 report argument also uses
its analytic and sign-variation hypotheses.

No exploratory high-order ODE probe output is included or replayed. The package
makes no claim about replacement asymptotics or periodic-orbit convergence.
The uniform-order argument has two exact computational components: the finite
bridge r=30–37 and the rational threshold inequalities for r >= 38. The report
supplies the analytic, cone-invariance, spectral-separation, and invariant-manifold
steps that turn those certificates into a theorem for every m >= 29. The finite
program does not claim to enumerate infinitely many orders.

Proof notes, audit notes, third-party papers, and exploratory probe logs are not
part of this bundle.
