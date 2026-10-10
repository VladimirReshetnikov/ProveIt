# A Complete Index-Three Lerch Phase Diagram

Research continuation for Vladimir Reshetnikov's **ProveIt** project. Prepared October 9, 2026 (America/Los_Angeles).

## Read first

The complete, self-contained article is [`article/lerch_global_phase.pdf`](article/lerch_global_phase.pdf); its editable source is [`article/lerch_global_phase.tex`](article/lerch_global_phase.tex).

The main result resolves **Conjecture 12.1** of the earlier report *Lerch Endpoint Singularities and Stieltjes Zero Bifurcations*: there is no additional outer pair of positive zeros in the index-three, first-parameter-derivative Lerch family. A global exterior inequality and a finite exact interval calculation complete the previously localized fold theorem.

Further proved results include an all-index exterior differential barrier, a sharp cutoff for its fixed operator, an asymptotic formula for that cutoff, an all-odd-index restriction on integer-separated zeros, and a sharp unit-span theorem. The span of the three cubic zeros is at most one, attaining one at a unique parameter with zeros exactly at 1 and 2. The article gives exact polylogarithmic order-derivative formulas for that parameter, the common branch velocity, and the negative span curvature. Strict span unimodality is a **conjecture**, not a theorem here.

These are ordinary mathematical proofs with finite exact-arithmetic certificates. They have not been verified by a proof assistant or independently refereed. Novelty is relative to the inspected manuscript and named companion; no exhaustive priority claim is made. No remote repository files were changed.

## Reproduce the proof-bearing computation

From this directory, with Python 3.10 or newer:

```sh
python3 code/verify_exact.py
python3 code/test_exact.py
```

Both commands use the Python standard library only. Do not use Python's `-O` or `-OO` flags: optimized execution disables assertions, and the verifier explicitly rejects it.

The verifier recomputes `certificates/exact.json`; it does not merely trust or replay stored answers. It checks four Euler--Maclaurin sign enclosures, explicit rational exponential bounds, a low-parameter positivity margin, and all 128 closed rational cells of a derivative inequality valid uniformly for `9/10 <= rho <= 1`. Each cell uses 64 summands and a proved infinite-tail upper bound. Every proof-bearing arithmetic operation is outward-rounded integer interval arithmetic at scale `10^60`; logarithms use a finite atanh series with an explicit rational remainder.

The largest upper bound over the entire derivative strip is less than `-0.0256107476350180`, hence strictly less than `-1/40`. This covers intervals, not sampled points. The proof also needs the analytic arguments in the article; the finite checks alone are not a proof of the infinite-parameter theorem.

The eight unit/regression tests include 1,000 randomized exact-rational interval checks, independent logarithm-series checks for the derivative polynomials, and anchor computations with a different Euler--Maclaurin truncation. Run receipts are included.

## Optional numerical diagnostics

```sh
python3 -m pip install -r requirements-optional.txt
python3 code/numerical_diagnostics.py
```

This produces `certificates/diagnostics.json`. It uses independent Laplace quadrature and Cauchy/Fourier differentiation of polylogarithms to examine the fold, resonance, velocities, curvature, and exterior cutoff. These are **non-certified numerical diagnostics**. In particular, the decimal approximations to the fold and resonance parameters are not isolating intervals and are not used by the proofs.

A naive tiny-step order differentiation produced a residual around `1.28e-17` at 40-decimal working precision in this environment. Its value is intentionally retained alongside the more accurate Cauchy/Fourier comparison. It is not represented as a 40-digit verification or as a formally established software defect.

## Build the PDF

With a standard TeX Live installation including `pdflatex`, `lmodern`, `amsmath`, `amsthm`, `mathtools`, `booktabs`, `microtype`, `hyperref`, `aliascnt`, and `cleveref`:

```sh
make pdf
```

Or run `pdflatex -interaction=nonstopmode -halt-on-error lerch_global_phase.tex` three times from `article/`. The supplied PDF is already compiled. No external figures, bibliography database, network access, or private fonts are needed.

## Integrate into ProveIt

See [`integration/INTEGRATION.md`](integration/INTEGRATION.md). The package includes an insertion fragment with distinct label prefixes and a guarded, dry-run-by-default correction helper. The proposed corrections change one wrong polynomial label and one duplicated phrase in the existing chapter; the notation issue was already identified by the earlier report and is not claimed as a fresh discovery.

The manuscript snapshot is pinned to commit:

```
cc34f73596336f2466d9754cb0f3635bd2bedade
```

The relevant zero-geometry chapter has Git blob SHA:

```
7f41eb87ed5e0bf90a2dffa489a8e2cd552056be
```

See `provenance/sources.json`, `provenance/claims.json`, and `MANIFEST.sha256` for source scope, evidence status, environment, and package hashes. The prior report's inspected TeX source is identified by hash, but is not duplicated in this package.

## Contents

- `article/`: the complete article, editable TeX and compiled PDF.
- `code/`: exact verifier, unit tests, optional diagnostics, guarded correction helper.
- `certificates/`: exact rational certificate, numerical diagnostics, execution and PDF validation receipts.
- `integration/`: manuscript insertion fragment, correction specification, integration instructions.
- `provenance/`: inspected source identifiers and claim/evidence ledger.
- `Makefile`, `requirements-optional.txt`: reproduction entry points.

The article's future-work section distinguishes the proved maximum from the stronger unproved unimodality conjecture; it also identifies optimized barrier coefficients, higher-index phase diagrams, certified critical-parameter enclosures, positive-measure generalizations, and formal verification as further research tasks. This package does not claim a solution of the separate S6 reduction problem or all-index saturation thresholds.
