> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part XII** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/q-fabius-parameter-deformations/Fabius_Flat_Parameter_Response_Dynamics/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Fabius–Rvachev flat-parameter response report

This directory preserves and normalizes the submitted research package
**“Flat Parameter Fronts, q-Susceptibility, and Smooth Dynamics: New Frontier Results in the
Fabius–Rvachev System.”** The normalization keeps the arrival record separate from the current
working ledger and corrects the mathematical status boundaries described below.

## Status of the mathematical claims

- The report proves, on paper, joint parameter–space smoothness and flat plateau fronts, the
  first parameter-response measure and its KR resolvent, the tangent refinement and Fourier
  formulas, response cumulants and moments, the Legendre coefficients, and the endpoint height
  \(B\).
- The higher-response differentiated identity is distributional. Its KR resolvent form for
  orders \(s\ge2\) is explicitly conditional on representing the differentiated source as a
  finite zero-mass measure.
- The flat \(C^\infty\) Koenigs convergence assertion is isolated as hypothesis (K), because
  the all-orders derivative estimates are not proved in the submitted argument. The global
  coordinate \(\Theta\), inverse-iterate asymptotics, escape clock, and periodic quotient with
  \(B\) are all conditional on (K).
- None of the new claims has an exact current Lean theorem. The existing Lean files certify
  fixed-parameter laws and smoothness, half-base identifications, shape/inverse/midpoint and
  endpoint inputs, and algebraic infrastructure only. See **REPOSITORY_AUDIT.md** for the exact
  crosswalk and overlap audit.

“Repository-novel” means only that an equivalent claim was not found in the audited active
primary exposition, canonical frontier synthesis, or current draft corpus. It is not a claim
of priority over the mathematical literature.

## Contents and provenance

- **fabius_frontier_report.tex** and **fabius_frontier_report.pdf** — normalized report source
  and its matching compiled PDF.
- **code/fabius_q_response_experiments.py** — symbolic and numerical replay program.
- **data/** and **figures/** — committed exact tables, Monte Carlo checks, and figures.
- **NUMERICAL_README.txt** and **EXPERIMENT_REPLAY.txt** — run parameters and replay comparison.
- **REPOSITORY_AUDIT.md** — claim-status and Lean-source crosswalk.
- **PDF_VALIDATION.txt** — final build and PDF validation record.
- **ARRIVAL_SHA256SUMS.txt** — immutable verbatim ledger from the submitted archive.
- **SHA256SUMS.txt** — exhaustive ledger of the current normalized package, excluding itself.

The submitted ZIP was **fabius_frontier_report_2026.zip**, 803,598 bytes, with SHA-256
**afdcf522589a7baad82c81a527c02dcc09e58455ab14c57a9c492e65563c647e** and Git blob
**ec8727448efff206724963f5b3922ff5b8f5fc61**. It contained one wrapper directory, 14 files,
and four directory entries; its 13-row internal ledger verified every payload file. The
arrival ledger is preserved unchanged even though normalized files now have new hashes.

## Rebuilding the PDF

From this directory, run exactly three strict serial passes on the frozen final source:

~~~bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
~~~

The document uses the repository’s canonical primary preamble: A4 paper, 27 mm margins, and
Libertinus fonts when available. The current 1,890-line source matches the 26-page PDF; its
exact identity, geometry, font, and text-extraction facts are recorded in
**PDF_VALIDATION.txt**. That receipt distinguishes the current structural checks from the
earlier log and all-page visual inspection rather than carrying obsolete source-line
coordinates forward. Remove LaTeX auxiliary files after validation.

## Reproducing the numerical layer

The committed run used Python 3.13.14 and the exact pinned versions in **requirements.txt**.
From the package root:

~~~bash
python -m pip install -r requirements.txt
python code/fabius_q_response_experiments.py \
  --output-root . \
  --samples 1000000 \
  --cdf-samples 1500000 \
  --chunk-size 25000 \
  --digits 32 \
  --q-step 0.005 \
  --seed 20260830 \
  --max-moment 14 \
  --max-legendre 20
~~~

These values are also the program defaults. Command-line options change the sample counts,
chunk size, digit truncation, finite-difference step, seed, maximum moment, maximum Legendre
degree, and output location; there is no separate precision option. Exact SymPy outputs are
deterministic. Monte Carlo tables are validation checks only and can exhibit harmless
last-bit floating-point variation; the recorded comparison and tolerances are in
**EXPERIMENT_REPLAY.txt**.
