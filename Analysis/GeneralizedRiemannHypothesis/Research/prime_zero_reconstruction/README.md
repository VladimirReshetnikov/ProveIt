# One Prime Signal for All Dirichlet Zeros

Research note, 26 November 2026.

## Contents

- `reconstruction.tex`: full LaTeX manuscript (theorem, proof, ordinary-prime corollary, finite-family converse, stability estimates, references and further research questions).
- `reconstruction.pdf`: compiled nine-page manuscript.
- `verify_code.py`: standard-library Python checks of rational coefficient recursion, exact interval arithmetic and prefix decoding, and a finite synthetic Fourier example.
- `verification.txt`: captured output from running the checks.
- `sources.md`: repository provenance, source review and scope of novelty search.
- `SHA256SUMS`: integrity hashes of the above files.

## Reproduce

    python3 verify_code.py
    pdflatex -interaction=nonstopmode -halt-on-error reconstruction.tex
    pdflatex -interaction=nonstopmode -halt-on-error reconstruction.tex
    pdflatex -interaction=nonstopmode -halt-on-error reconstruction.tex
    sha256sum -c SHA256SUMS

The hash check is for the delivered snapshots; regenerated PDF metadata may differ. The code does not require Mathlib or Lean. Its synthetic multiplicities are NOT actual L-function zeros. The exact interval checks cover two finite prefix boxes, not the analytic proof or the infinite theorem. All analytic arguments appear in the manuscript. The result uses the exported Dirichlet GRH theorem; neither its upstream Lean build nor a new Lean formalization was executed here. The novelty assessment is provisional. The exact autocorrelation theorem is not a practical finite-data zero-finding algorithm.
