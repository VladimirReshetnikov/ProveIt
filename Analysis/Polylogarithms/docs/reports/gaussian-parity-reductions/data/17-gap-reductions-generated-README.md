# Generated parity formulas

`parity_tables.tex` is an input fragment, not a standalone document. It requires
AMS math support and uses ordinary `F`, `\rho`, `\Re`, and `\Im` notation.
`parity_tables.json` records the corresponding SymPy expression strings.

Conventions:

- F_(a,b)(z) = Li_(a,b)(z,1) in decreasing-index order.
- rho = exp(2 pi i / 3).
- B_(2r) = beta(2r), including B_2 = Catalan's constant.
- C_(2r) = Im Li_(2r)(rho).
- ell_2 = log(2); ell_3 = log(3).

There are 56 formulas: for each weight 2 through 8, all w-1 index pairs at each
of two roots. The selected projection is imaginary at even weight and real at
odd weight. These are consequences of the proved parity formula, not unrelated
PSLQ conjectures. Their names and ordering are deterministic under the recorded
SymPy version. Regenerate with `python src/symbolic_checks.py`.

The source theorem applies at all weights. This finite table neither establishes
an independence result nor limits the range of the theorem.

The companion `parity_tables.pdf` is compiled from `parity_tables_document.tex`.
From this directory run `pdflatex -jobname=parity_tables parity_tables_document.tex`
twice to rebuild it. The main bundle Makefile also supplies `make tables`.
