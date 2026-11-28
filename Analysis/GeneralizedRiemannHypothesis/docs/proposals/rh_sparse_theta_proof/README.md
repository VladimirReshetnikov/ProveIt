# Sparse cutoffs and averaged twist selection

Research note accompanying the supplied guide *How theta lifts locate the zeros of Dirichlet L-functions*.

- `sparse_theta_proof.pdf`: compiled mathematical report, including proofs of reciprocal convexity interpolation, fourth-power and dyadic-grid reductions, local-average variant, Gaussian second moment and sharpened twist selection, and combined sufficient criterion for RH/Dirichlet GRH.
- `sparse_theta_proof.tex`: complete LaTeX source. Compile three times with `pdflatex -halt-on-error sparse_theta_proof.tex` (or use `latexmk -pdf`).
- `check_sparse_reduction.py`: Python 3 standard-library regression tests of the finite identities, grid and exponent arithmetic. Run `python3 check_sparse_reduction.py`.
- `checks.txt`: recorded output of these checks.
- `LEAN_PLAN.md`: suggested implementation and validation steps (not compiled Lean code).
- `source-audit.tsv`: source files inspected through the GitHub connector, with Git blob IDs and links. The old vendor path now points to `Lean/grh`. Selected recorded identifiers match the supplied guide; no full-tree verification was performed here.

The reductions do **not** replace the deep arithmetic determinant estimates, and no claim is made that the restricted data construction has already been simplified. The arithmetic proof in the upstream package supplies the original hypotheses. The changes proposed here allow a weaker sufficient hypothesis and shorten/reorganize the analytic route. No Lean kernel replay was performed for the new arguments; the numerical checks are not formal proof. No change to GitHub was made. Independent verification of the original/readable proof: https://math.mit.edu/~drew/shortgrh/ .
