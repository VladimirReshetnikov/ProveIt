# Sharp multiscale prime-window inequalities

- `paper.tex`: mathematical note and proof.
- `paper.pdf`: compiled note.
- `check_windows.py`: numerical illustration of the finite prime-power formula, contrast bound and Gram determinant. Python 3.8+ and `mpmath` are required.
- `example.txt`: actual output of the script (not certified intervals).
- `SOURCES.md`: source audit with inspected GitHub blob identifiers and literature links.

Reproduce the PDF with `pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice. Reproduce the example with `python check_windows.py`. The mathematical argument assumes the Dirichlet GRH endpoint, which the inspected repository reports as formally proved, and standard Weil explicit formula. It is not a new Lean-checked theorem. The compact window/contrast formulation is a candidate new result, not a certified literature priority claim.
