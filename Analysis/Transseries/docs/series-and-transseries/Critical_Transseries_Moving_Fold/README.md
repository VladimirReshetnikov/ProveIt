# Critical Transseries at a Moving Fold

**A uniform two-sheet atlas, large-sector crossover, and resonant action splitting**  
Research continuation for the ProveIt project, 29 September 2026.

## Main result and scope

The article resolves the predecessor manuscript's Research question 11.8 for the
independent-parameter equation

    delta + log(1 + delta/w) + w*z*exp(-delta) = 0.

It proves an exact local two-sheet atlas, locates the moving critical value,
constructs all-order polynomial profiles with an explicit uniform error bound,
and derives a joint critical/large-sector limit. A second theorem treats
convergent analytic folds driven by finitely many exponential actions, including
resonance cancellations and a constructive finite positive support grid.

The original fixed-coupling map has the specialization z = exp(-w)/w, which tends
to -e as w tends to -1. The small-(w+1,z) chart is consequently NOT a claimed
analysis of that fixed-coupling specialization at its core critical point.
The article explains this distinction prominently.

The square-root preparation mechanism and singularity-analysis methods are
classical. The quantitative specialization, all-order profile construction,
specific crossover, and support construction are the contributions developed
here. Independent mathematical and priority review remain appropriate. No new
Lean formalization, peer review, or general resurgence theorem is claimed.

## Files

- `article.tex`: complete editable LaTeX manuscript, with bibliography.
- `article.pdf`: compiled article.
- `verify.py`: exact symbolic checks and 100-decimal-digit numerical diagnostics.
- `data/verification.json`: complete machine-readable results and package versions.
- `data/verification_run.txt`: stdout from the full verification run.
- `data/runtime.txt`: observed elapsed runtime in the preparation environment.
- `data/profile_table.tex`, `data/crossover_table.tex`: generated article tables.
- `requirements.txt`: Python dependencies, pinned to the versions used.
- `Makefile`: convenient verification and PDF build targets.
- `PROVENANCE.md`: inspected sources, repository pin, and audit boundaries.
- `SHA256SUMS`: hashes of the package files other than the ledger itself.

The PDF can be rebuilt without running the Python code because its generated
table fragments are included. No external font files are bundled.

## Reproduce

Use Python 3.10 or later and a TeX Live installation with pdfLaTeX and latexmk.
The verified environment used Python 3.13, SymPy 1.14.0, and mpmath 1.3.0.

```sh
python -m pip install -r requirements.txt
python verify.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, `make verify` and `make pdf` run the corresponding commands.
The default verification run includes sector indices up to 400. Running
`python verify.py --quick` omits the n=400 diagnostics and intentionally writes
shorter tables; the exact symbolic checks are unchanged. The default full run
is the one used for the supplied PDF and data.

The script requires no network access after dependency installation. Output
paths are relative to the script's own directory, not the caller's working
directory. It replaces only its own JSON and generated table files; it does
not update the ProveIt repository or any Library source.

## What was checked

Exact rational symbolic checks cover the critical equation through degree 8,
the normalized critical value through degree 5, five profile polynomials,
the singular amplitude through degree 4, branch-point reversion, the logarithmic
drift coefficients, and all rational domain majorants. Numerical diagnostics
cover the fold and nearby points, the first three known rational sector
functions, the large-sector crossover, and a resonant discriminant example.

All executed checks passed. These diagnostics do not certify the analytic
existence and all-order assertions: the article provides mathematical proofs
for those. The numerical roots are not interval-arithmetic enclosures.
The PDF was checked for compilation warnings, unresolved references, layout,
and embedded fonts. The supplied build has no overfull or underfull boxes.
