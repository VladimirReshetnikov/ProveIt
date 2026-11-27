# Sharp Hermite-threshold constants

Research note, 27 November 2026. Main result: exact oscillatory leading constant for every Hermite threshold; uniform left critical window; top-layer rigidity; Dirichlet-GRH prime application.

## Files and reproducibility
- `paper.tex` — complete LaTeX source, bibliography included.
- `paper.pdf` — compiled eight-page paper.
- `check.py` — standard-library Python 3.9+ exact rational certificate checker, for j=2 and j=3. Floating-point calculations only propose bracket locations and display decimals; all actual certificate checks use integers or fractions.
- `checks.txt` — output from `python check.py`, with 16 successfully verified instances. The displayed scaled lower and upper values are rounded decimal displays of exact rational bounds; the predicted value is not a finite-dimensional exact equality. The proof establishes asymptotics independently of this computation.
- `sources.md` — source file inventory and scope.

Build: `pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice. Run `python check.py` (or pass `--k 4096 16384` for selected sufficiently large dimensions). The layer construction is guaranteed for sufficiently large k, not all small inputs; the checker refuses negative weights or invalid grids.

The lower certificate is a polynomial times a square, nonpositive on every allowed layer by a parity inequality; its Fourier coefficients are computed exactly. The upper certificate consists of nonnegative rational weights with matched moments, followed by an exact scan over all Walsh degrees using Krawtchouk recurrences. Symmetry ensures this checks all individual parity characters, not just a sample. The selected k include perfect squares and nearby values to illustrate the oscillation.

## Status
The main combinatorial results are unconditional. The prime application uses the source Dirichlet GRH theorem and a standard smoothed explicit formula; it does not claim a new GRH or an improved exponent at the exact threshold. The global priority of the asymptotic formula has not been established. The new proofs are not Lean-formalized; the vendored GRH proof was not rebuilt or independently audited in this task. The right critical window is left open. No changes were made to the GitHub repository.
