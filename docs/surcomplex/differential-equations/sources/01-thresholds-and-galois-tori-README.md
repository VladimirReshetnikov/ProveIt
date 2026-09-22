# Differential Surcomplex Numbers

## Bounded Phase, Oscillation Obstructions, and Rank-One Differential Equations

A 24-page article prepared for Vladimir Reshetnikov, with a standalone LaTeX
source, compiled PDF, and exact finite regression checks.

## The selected documentation gap

The inspected Surreal repository already distinguishes external-variable
function differentiation from a derivation of the surreal scalar field. Its
analysis report also proves an incompatibility for its chosen canonical global
surcomplex exponential. Those are prior coverage, not missing results.

This article develops the internal differential equations themselves: the exact
image of the logarithmic derivative, a criterion for every rank-one equation,
canonical gauge forms, the missing oscillatory modes, and explicit
Picard–Vessiot extensions. The audit is targeted and revision-specific, not an
exhaustive review of every preserved source draft.

Repository snapshot:

    VladimirReshetnikov/Surreal
    e260237db9b71da8b74a0c13c8e6355119091100

## Main mathematical results

Throughout, the derivative is the simplest Berarducci–Mantova derivation,
normalized by d(omega) = 1. Its published construction and integration theorem
are imported, not reproved.

* A nonzero solution of d(y) = a*y exists in No[i] exactly when Im(a) has a
  finite real primitive. Equivalently, its normalized primitive has zero
  purely infinite part.
* That infinite part is a complete invariant of rank-one equations under
  base-field gauge transformations. It gives an exact obstruction sequence.
* In the real-exponent Hahn subfield, the imaginary coefficient has a finite
  primitive exactly when its least exponent is strictly greater than 1
  (or the coefficient is zero). Iterated logarithms give finer thresholds;
  the real-exponent valuation test must not be used globally.
* The homogeneous solutions of an ordinary complex constant-coefficient
  operator contain precisely its real exponential modes, with their usual
  polynomial multiplicities. In particular, d²(y) + y = 0 has only the zero
  solution in this field.
* An upper-triangular system has a fundamental matrix in the base field
  exactly when all its diagonal rank-one obstructions vanish.
* Missing rank-one solutions have explicit rational Picard–Vessiot extensions
  with no new constants. For diagonal systems, integer relations among the
  phase obstructions determine the differential Galois torus.

The proofs distinguish scalar differentiation, formal differentiation, and
external-variable analytic functions throughout. A final localization theorem
provides set-sized differential workspaces; no class of proper-class cosets or
proper-class automorphism maps is formed.

## Files

- `article.pdf`: finished 24-page article.
- `article.tex`: standalone source, with internal bibliography.
- `code/verify.py`: exact standard-library Python verification program.
- `data/verification.json`: actual recorded run, 1,395 checks passed.
- `data/source_audit.json`: repository snapshot, inspected sources, and
  mathematical input ledger.
- `data/proof_status.json`: proof and validation boundaries.
- `data/build_report.json`: PDF build and layout checks.
- `build.sh`, `build.ps1`: POSIX and PowerShell reproduction scripts.
- `SHA256SUMS.txt`: hashes of the delivered files other than this manifest.

## Reproduce the checks

Python 3.9 or later, no third-party packages:

    python code/verify.py

On systems that name Python 3 separately:

    python3 code/verify.py

A custom output destination is supported:

    python code/verify.py --output results/local-checks.json

The bundled run used Python 3.13.5, deterministic seed 20260921, and formal-series
cutoff 16. All 1,395 checks passed. These are exact finite Laurent-algebra and
truncated-series tests, not a proof of the infinitary theorems. The recorded
Python version will naturally change when the program is run elsewhere.

## Rebuild the article

Install a TeX distribution providing the packages declared in `article.tex`.
No external bibliography database, graphics, shell escape, network download,
or separate font files are needed.

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

When `latexmk` is unavailable, run the following command three times:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex

The supplied build scripts run the checks first and use this fallback. In a
POSIX shell, use `sh build.sh`; in PowerShell, use `./build.ps1` under the local
script-execution policy. The scripts do not install software or modify that
policy. The PowerShell script is supplied but was not executed on Windows in
this preparation environment.

The delivered PDF was built with pdfTeX 1.40.26, TeX Live 2025/dev/Debian,
and latexmk 4.86. The final build had no LaTeX warnings, undefined references
or citations, or overfull/underfull boxes. Rebuilding can change PDF metadata
and file hashes without changing the mathematics.

## Status

This is an exposition with proofs, not a claim of novelty or priority and not
a claimed solution to a named published open problem. The targeted literature
search was not exhaustive. The article has not been independently refereed or
checked by a proof assistant. Executable checks do not verify the
Berarducci–Mantova construction, arbitrary Hahn summability, proper-class
statements, or the general differential Galois arguments.

The remote repository was not modified. No third-party papers or font files
are included in this package.
