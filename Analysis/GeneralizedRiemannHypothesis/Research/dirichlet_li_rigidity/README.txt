Identifying a Dirichlet character from filtered Li coefficients
26 November 2026

paper.pdf          Research note, full proofs, examples and references
paper.tex          Self-contained LaTeX source of the research note
verify.py          Fourier sampling, aliasing, finite filter recovery and a
                   two-ordinate illustration using zeta zeros
check_shells.py    Synthetic off-circle tests of reflection, integer rounding
                   and detection on translated intervals
checks.txt         Output of both scripts, in the order shown below

Rebuild the paper with a standard TeX Live installation:
  pdflatex paper.tex
  pdflatex paper.tex

Reproduce the finite numerical checks with Python 3:
  python3 verify.py
  python3 check_shells.py

The scripts use only the Python standard library. They illustrate individual
identities and bounds. The infinite-data theorem is proved in paper.tex.
No Lean formalization of the inverse theorem is included. The paper links
to the precise upstream revision for Dirichlet GRH.
