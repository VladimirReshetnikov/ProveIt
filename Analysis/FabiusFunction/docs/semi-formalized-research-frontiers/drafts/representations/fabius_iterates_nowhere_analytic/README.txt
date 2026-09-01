NOWHERE ANALYTICITY OF FABIUS COMPOSITIONAL ITERATES
====================================================

Main files
----------
- fabius_iterates_nowhere_analytic.tex : complete LaTeX source
- fabius_iterates_nowhere_analytic.pdf : rendered report
- numerical_experiments.py            : commented reproducible diagnostics

Numerical output
----------------
The numerical_output/ directory contains the CSV, metadata, and four generated
plots.  The script synchronizes those four plots into figures/; the LaTeX report
embeds fabius_iterates.png, spine_comparison.png, and spine_remainder.png, while
taylor_root_diagnostic.png remains a synchronized supplementary diagnostic.

Repository review and status boundary
-------------------------------------
The companion REPOSITORY_AUDIT.md records the post-intake claim review.  That
review found no fatal gap and repaired three proof-exposition defects in the TeX:
it made the weighted partition-defect decay uniform, placed the outer function's
smoothness hypothesis near h(x), and made the n = 1 tie set literally empty.  It
also corrected the source map from the nonexistent StrictMonotonicity.lean to the
live Monotonicity.lean module.

The report now contains 15 nonconjectural labelled manuscript results, two
numbered warning quarantines, and one live conjecture.  Former Conjecture 14.1
is nonexclusive as submitted, and no replacement zero-radius/eventually-zero
classification is asserted.  Former Conjecture 14.2 is discharged by the
manuscript's exact tie proposition: orders m = 6l + 4 give a surviving amplitude
Up(1/9) >= 1/2 and force zero Taylor radius at every tie point.  Lean supplies
the exact quarter-value anchors and the finite positive-list defect arithmetic,
but the tie proposition, n >= 2 iterate theorem, set-partition wrapper, and new
finite-spine machinery remain unformalized.  Neither manuscript labels nor
numerical replay establish Lean status.

Reproduce the numerical diagnostics
-----------------------------------
MPLBACKEND=Agg python numerical_experiments.py \
  --output-dir numerical_output --figure-dir figures \
  --x0 0.437123456789 --iterate-count 4 --max-order 22

Dependencies: Python 3, NumPy, SciPy, Matplotlib.
The CSV writer fixes LF line endings on every platform.  Exact PNG bytes and
the last floating-point digits require the pinned Linux/Python environment in
REPOSITORY_AUDIT.md; other environments should be checked numerically, not by
requiring identical hashes.  No numerical result is a premise of the proof,
and the floating-point replay is not independent symbolic verification.

Formalization status
--------------------
The report crosswalks the exhaustive three-definition, thirty-three-theorem
`PartitionDefect.lean` API.  That Lean module proves the
finite positive-list defect decomposition, zero and sharp-equality
classifiers, fixed-block lower bound, and first positive shell.  It does not
construct set partitions, prove the weighted Bell sum or its asymptotics, or
prove nowhere analyticity for any positive compositional iterate; those
manuscript steps remain paper-only.

Before repository LF normalization, the audit reproduced all six submitted
outputs byte-for-byte in the fully pinned Ubuntu 22.04/CPython 3.12.13
environment documented in REPOSITORY_AUDIT.md.  Cross-platform replay retained
scientifically stable values but showed byte-level floating-point and plot drift.
The delivered computation is a finite-order floating-point/FFT diagnostic, not
symbolic verification or proof.  The repaired script fixes CSV records to LF and
synchronizes all four PNGs into figures/.  The Taylor-root plot remains
supplementary rather than embedded; only up(0) and F(1/2) are tolerance-checked;
and the CSV's relative_gap denominator differs from the paper table and
remainder plot.  The audit preserves the submitted CRLF hash, current tracked
hashes, pinned dependency list, and exact conventions.

Compile the report
------------------
From a clean directory, run exactly three serial passes:

pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_iterates_nowhere_analytic.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_iterates_nowhere_analytic.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_iterates_nowhere_analytic.tex

The source uses the repository's canonical A4, 27 mm, Libertinus preamble.
After a successful build, inspect every rendered page and remove the generated
.aux, .log, .out, and .toc sidecars before committing the matching PDF.

Validated repository build (2026-08-31)
---------------------------------------
- Exactly three strict serial passes from clean auxiliary state produced a
  22-page A4 PDF from the frozen 1,542-line, 63,320-byte source with SHA-256
  c0684c7c790d9e1b2b569d49d4d2a294aabc409c23a74f8cc1cdc5eb83ff6384.
- The retained PDF is 786,569 bytes with SHA-256
  46244adfe1289f318b76b306ae0b11f751425488b1099c785c85ad3dcba45b08.
- The final log has no warnings, errors, unresolved references, rerun requests,
  duplicate destinations, or overfull/underfull boxes.
- All 22 font rows are embedded and subset Type 1 fonts; five are Libertinus,
  with no Type 3 or Latin Modern font.
- Every page has extractable text and A4/zero-rotation geometry.  All 22 pages
  were rendered and visually inspected, including the status box, exhaustive
  Lean crosswalk, exact tie proposition, two quarantine warnings, sole live
  conjecture, figures, and source map.
- Title, author, subject, and keywords metadata are present.
- The numerical script and Lean sources were not rerun.  The four tracked
  figure pairs remain byte-identical.
