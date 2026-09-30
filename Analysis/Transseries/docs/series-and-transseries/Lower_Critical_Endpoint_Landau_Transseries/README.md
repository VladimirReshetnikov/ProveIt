# Through the Lower Critical Endpoint
## Exponentially Coalescing Folds, Landau Transseries, and Conditional Action Budgets

A 25-page research article prepared for Vladimir Reshetnikov, 29 September 2026.

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
- `make_figures.py`: optional figure regeneration.
- `data/verification_results.json`: complete recorded verification report.
- `data/*.csv`, `data/figure_curve.json`, `data/run.log`: recorded data and log.
- `notes/provenance.json`: repository commit, inspected scope, and primary sources.
- `notes/proof_status.md`: assumptions and limitations by result.
- `notes/build_report.json`: compilation, rendering, and artifact hashes.
- `requirements.txt`, `build.sh`: reproduction aids.
- `SHA256SUMS`: checksum ledger for the delivered package, excluding itself.

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

The default output is also `build/verification`; it leaves recorded `data/`
files unchanged. The original run used Python 3.13.5 with the pinned
requirements. Optional `python make_figures.py` overwrites the figures and
`data/figure_curve.json`, using the recorded verification report.

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
