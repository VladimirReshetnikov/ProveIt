NOWHERE ANALYTICITY OF FABIUS COMPOSITIONAL ITERATES
====================================================

Main files
----------
- fabius_iterates_nowhere_analytic.tex : complete LaTeX source
- fabius_iterates_nowhere_analytic.pdf : rendered report
- numerical_experiments.py            : commented reproducible diagnostics

Numerical output
----------------
The numerical_output/ directory contains the CSV, metadata, and generated plots.
The figures/ directory contains copies used by the LaTeX report.

Repository review and status boundary
-------------------------------------
The companion REPOSITORY_AUDIT.md records the post-intake claim review.  That
review found no fatal gap and repaired three proof-exposition defects in the TeX:
it made the weighted partition-defect decay uniform, placed the outer function's
smoothness hypothesis near h(x), and made the n = 1 tie set literally empty.  It
also corrected the source map from the nonexistent StrictMonotonicity.lean to the
live Monotonicity.lean module.

The report now contains 14 nonconjectural labelled manuscript results, two
numbered warning quarantines, and one live conjecture.  Former Conjecture 14.1 is
not exclusive at an n = 1 interior dyadic point: the same finite Taylor polynomial
has positive radius and fails to represent F locally.  Former Conjecture 14.2 is
already discharged by the exact quarter-point facts and the report's
binary-transition lemma.  These dispositions are stated directly in the TeX.
Neither manuscript labels nor numerical replay establish Lean status; the n >= 2
iterate theorem and its new finite-spine machinery remain unformalized.

Reproduce the numerical diagnostics
-----------------------------------
python numerical_experiments.py --output-dir numerical_output \
  --x0 0.437123456789 --iterate-count 4 --max-order 22

Dependencies: Python 3, NumPy, SciPy, Matplotlib.
No numerical result is used as a premise of the proof.

The repository audit reproduced all six outputs byte-for-byte in a fully pinned
Ubuntu 22.04/CPython 3.12.13 environment documented in REPOSITORY_AUDIT.md.
Cross-platform replay retained scientifically stable values but showed byte-level
floating-point and plot drift.  The delivered computation is a finite-order
floating-point/FFT diagnostic, not symbolic verification or proof.  The script
writes plots only to numerical_output/ while TeX reads figures/, so regeneration
requires an explicit copy step.  The delivered taylor_root_diagnostic.png is not
included by TeX; only up(0) and F(1/2) are tolerance-checked in code; and the CSV's
relative_gap denominator differs from the paper table and remainder plot.  See
REPOSITORY_AUDIT.md for the pinned dependency list, hashes, and exact conventions.

Compile the report
------------------
From a clean directory, run exactly three serial passes:

for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    fabius_iterates_nowhere_analytic.tex
done

Validated repository build (2026-08-30)
---------------------------------------
- 19 A4 pages using the canonical 27 mm geometry and Libertinus prose.
- All PDF fonts are embedded and subset Type 1 fonts; no Type 3 fonts occur.
- The final log has no warnings, unresolved references, or overfull/underfull boxes.
- All pages have extractable text and render successfully; the title/status box,
  theorem boundary, numerical figures, quarantine warnings, live conjecture, and
  source map were inspected visually.
- The source map names the live Monotonicity.lean module.
- The numerical script and Lean sources were not rerun during document-policy
  normalization; the supplied PNG figures and their numerical_output copies remain
  byte-identical.
