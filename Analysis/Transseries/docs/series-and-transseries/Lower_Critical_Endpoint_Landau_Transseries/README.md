# Through the Lower Critical Endpoint
## Exponentially Coalescing Folds, Landau Transseries, and Conditional Action Budgets

A 26-page research article (25 pages as delivered; see the amendments below)
prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

`article.pdf` is the compiled article. `article.tex` is its editable source;
the figures needed for rebuilding are included in `figures/`.

The paper addresses the interior-fold part of the lower-endpoint question
(alpha tending to 1) explicitly left open in ProveIt's **Beyond Finite-Action
Folds** package. It does not claim to settle the boundary-critical and
subcritical paths without an interior fold.

## Model and results

The model is

    U(q) = c Li_(2+epsilon)(q exp(U(q))),   epsilon >= 0.

The exact fold coordinate is delta > 0, with

    c = 1 / Li_(1+epsilon)(exp(-delta)),
    A = c Gamma(1-epsilon) delta^epsilon,
    lambda = n A delta.

The main results are:

- An exact convergent normal form and a uniform coefficient crossover theorem
  through epsilon = 0, with no restriction on epsilon log(1/delta).
- At epsilon = 0, the scale delta = -log(1-exp(-1/c)) ~ exp(-1/c), an explicit
  Landau-density profile, and every finite-order coefficient correction.
- A convergent exponential-scale Lambert inverse and a uniform two-sheet fold
  chart. A separate Gaussian theorem identifies the first matching correction:
  a relative factor exp(ell/4) when lambda delta tends to ell.
- A limiting conditional action-cutoff profile R(lambda,m), with m = M delta;
  coefficient preservation in a compact crossover window holds exactly when
  M delta tends to infinity.
- The sharp limiting loss

      1 - R(lambda,m) ~ sqrt(lambda/(2*pi)) / (H(lambda)*m^2)
                       * exp(-m/(2*lambda) - lambda*exp(m/lambda)).

  Thus the small-tolerance scaled budget is double-logarithmic. This is a
  limiting-profile result, not an unproved finite-n accuracy certificate.

The article contains full conventional proofs, worked examples, ten further
research directions, a proof-dependency audit, and source provenance.

## Contents

- `article.tex`, `article.pdf`: source and compiled article.
- `figures/`: the two figures in PNG and PDF form.
- `verify.py`: exact algebraic tests and numerical diagnostic driver.
- `make_figures.py`: optional figure regeneration (writes under `build/`
  unless `--output-dir .` is given).
- `data/verification_results.json`: complete recorded verification report.
- `data/*.csv`, `data/figure_curve.json`, `data/run.log`: recorded data and
  the recorded standard output of the verification run.
- `notes/provenance.json`: repository commit, inspected scope, and primary sources.
- `notes/proof_status.md`: assumptions and limitations by result.
- `notes/build_report.json`: compilation, rendering, and artifact hashes of
  the delivered build.
- `requirements.txt`, `build.sh`: reproduction aids.

The delivered checksum ledger `SHA256SUMS` was verified in full (21/21) on
filing (batch 51) and not kept; the delivered archive remains in the
repository history (see `docs/incoming/README.md`, batch 51 row).

## Build

From the package directory:

```sh
sh build.sh
```

This runs three `pdflatex` passes into `build/` and copies the PDF to
`article.pdf`. The bibliography is embedded; no bibliography processor,
repository checkout, network access, or private fonts are needed. Keep the
included `figures/` directory beside the source.

On systems without a POSIX shell, run three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

## Reproduce the checks

```sh
python -m pip install -r requirements.txt
python verify.py --output build/verification --max-n 2048
```

The default output is also `build/verification` (relative to the working
directory); it leaves recorded `data/` files unchanged. The original run
used Python 3.13.5 with the pinned requirements. The recorded `data/` files
and `data/run.log` come from a run with `--output data` (the last line of
`data/run.log` is "Wrote data/verification_results.json"); the documented
command writes under `build/`.

Optional `python make_figures.py` regenerates the figures and
`data/figure_curve.json` from the recorded verification report. Since the
editorial amendment below it writes them under `build/` (`build/figures/`,
`build/data/figure_curve.json`; relative `--output-dir` paths are resolved
against the package root); only `python make_figures.py --output-dir .`
overwrites the shipped figures and `data/figure_curve.json`, as the
delivered script always did.

The build report `notes/build_report.json` describes the delivered build:
its digests of `article.tex` and `article.pdf` became stale when the source
was amended and the PDF rebuilt on filing, and its
`"rerun_json_and_csv_byte_identical": true` holds on the delivering (Linux)
platform. On Windows, where NumPy `longdouble` is double precision, a rerun
reproduces the recorded numbers only up to their last digits. A rerun on a
copy on 2026-09-29 (Windows) passed all 43 exact assertions and the 24
normal-form comparisons; the four CSVs and `verification_results.json`
differed from the recorded files only in floating values: normalized
coefficients and cutoff ratios agree to a relative 1.1e-13, and the small
residuals computed from them (`relative_error_1`, `relative_error_2`, of
size down to 1e-10) inherit that absolute noise; `figure_curve.json` agreed
to a relative 5.2e-13. The exact results agree everywhere. At larger
`--max-n` the explicit underflow error described below can fire there.
Where bare `python` does not resolve (as on this Windows checkout), use `py`
or `uv run --no-project --with-requirements requirements.txt python`.

The supplied run passes **43 exact assertions** and **24 high-precision
normal-form comparisons**. It records nine finite coefficient cases, nine
cutoff cases, six large-lambda profile cases, and four Palm-integral cases.
For lambda = 1 and n = 2048, the absolute relative residual falls from about
1.26e-3 to 1.54e-9 after the first two correction terms.

The probability recurrence uses NumPy `longdouble` for exponent range. A
platform with insufficient range triggers an explicit error if the initial
probability underflows. Large orders can require a wider-range implementation.
The coefficient computation is quadratic in each target order; the exact
small-degree audit is independent of that floating-point recurrence.

## Mathematical and priority status

These are conventional proofs in an AI-assisted research draft, not a
refereed publication or a Lean-verified development. Lagrange inversion,
conditioned Poisson allocations, the Landau law, saddle integration, and
Poisson insertion are classical and explicitly credited. The proposed
contributions are the model-specific confluent theorem, correction calculus,
matching threshold, and conditional cutoff analysis. Global publication
priority has not been established.

Floating-point checks and figures are diagnostics, not interval certificates.
Finite experiments do not replace quantified proofs. The small-tolerance
budget is a sequential statement about the limiting profile, not a certified
finite-n rule at arbitrary tolerances. No repository content was changed.

## Repository snapshot

`VladimirReshetnikov/ProveIt`, commit
`9250bbf8af80dacf7b252d9d0320b122c80961ba`.

The inspection included the full critical-Hahn package README and the
beginning of its article, plus selected project and package summaries. The
long article's connector output was truncated. This package does not claim
an exhaustive audit of the repository or its large canonical volume.

## Editorial amendments (ProveIt, 2026-09-29)

These changes were made on filing, after the batch-51 delivery. Every change
to the article text is marked in `article.tex` by a comment beginning
`% ed. (2026-09-29)`; visible additions are headed "Editorial note (ProveIt,
2026-09-29)".

- `article.tex`:
  - an unnumbered `ednote` environment for editorial notes (no numbering
    changes);
  - Section 1.1: the bibliography entry `repo-index`, previously never
    cited, is cited beside `repo-critical`; an editorial note records that
    the same lower endpoint is posed independently as Question 10 of the
    confluent package
    (`../Confluent_Critical_Transseries_Exponent_Two_Boundary/`) and
    Question 8 of the logarithmic-endpoint package
    (`../Logarithmic_Critical_Endpoint_Lambert_Charts/`), and that
    Theorem 3.1, Corollary 8.2 and Theorem 9.2 answer both for the pure tail
    on the interior-fold side only;
  - after the proof of Theorem 7.1: an editorial notation dictionary to the
    critical-Hahn article (`a = 1`, no prefix, `beta = c`,
    `alpha = 1 + epsilon`; its `beta_c` is `c_b`, its `rho_beta` is `rho_0`,
    its `A(t)` is the generating function `Li_(2+epsilon)(t)`, not the
    amplitude `A`; its `delta_beta = 1 - beta d_1` is a coupling mismatch,
    not the fold distance `delta` used here), with the agreement checked on
    filing: the exact fold reduces to its `eq:emerging-x`, the Gaussian law
    has the shape of its `eq:supercritical`, and its cutoff criterion is in
    a different regime;
  - Section 11.5: an editorial note that the slowly varying tail at fixed
    `1 < alpha < 2` is treated by the later package
    `../Slowly_Varying_Action_Tails_Critical_Transseries/` (batch 50), which
    this article could not see;
  - Section 12.4: an editorial note on the changed default of
    `make_figures.py`, the `--output data` origin of the recorded `data/`
    files, and the stale digests of the build report.
- `article.pdf`: rebuilt from the amended source (26 pages; the delivered PDF
  had 25; no errors, undefined references, multiply defined labels or
  duplicate destinations; no Type 3 fonts).
- `make_figures.py`: new option `--output-dir` (default `build`, resolved
  against the package root); only `--output-dir .` overwrites the shipped
  figures and `data/figure_curve.json`. A default run on a copy left every
  recorded file untouched; `--output-dir .` rewrote them as before.
- `notes/build_report.json`: not edited; it describes the delivered build
  (see "Reproduce the checks").
- `README.md`: the retired checksum ledger is no longer listed; the origin
  of `data/run.log`, the scope of the build report and the Windows rerun
  are documented; the page count is updated; this section.

### Batch-52 cross-reference notes (ProveIt, 2026-09-29)

Added when batch 52 was filed; marked in the source by `% ed. (2026-09-29,
batch 52)` comments.

- `article.tex`: an editorial note at the end of Section 11.1 ("The
  boundary-critical side of the lower endpoint"): the path
  `c = 1/zeta(1+eps)`, and with a fixed finite prefix `P`
  `c = 1/(zeta(1+eps) + P'(1))`, is treated for `eps_n -> 0` at any rate by
  two independent packages of batch 52,
  `../Lower_Critical_Endpoint_Cauchy_Cutoff_Condensation/` and
  `../Lower_Critical_Endpoint_Uniform_Coefficients_Compound_Poisson/`, which
  prove the same theorem (uniform coefficient law, one exceptional action, a
  Landau cutoff profile for `n eps -> infinity`, a compound-Poisson deficit
  for bounded `n eps`). The Landau law of the second is the law with this
  article's density `p` (`eq:landau`); that of the first is its shift by
  `1 - gamma`. Neither matches its results to the `delta > 0` chart here;
  the subcritical paths `c < 1/zeta(1+eps)`, a theorem uniform across
  `c = 1/zeta(1+eps)`, and that matching remain open.
- `article.pdf`: rebuilt (26 pages, unchanged; no errors, undefined
  references, multiply defined labels or duplicate destinations; no Type 3
  fonts). `notes/build_report.json` still describes the delivered build.
- `README.md`: this subsection.
