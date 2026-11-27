# Distinguishing Dirichlet characters and abelian number fields by low zeros

The full paper is in `zero_windows.pdf`, with its self-contained LaTeX source
in `zero_windows.tex`. Theorems 1 and 2 use the Dirichlet zero-line theorem
at the pinned upstream revision. Proposition 6 gives an unconditional
interval certificate for a concrete pair of biquadratic fields.

## Build the paper

In this directory, run the following commands with a standard TeX Live installation.

```sh
pdflatex -halt-on-error zero_windows.tex
pdflatex -halt-on-error zero_windows.tex
```

The bibliography is part of the TeX file.

## Reproduce the computations

Use Python 3.9 or later. All three programs run with the standard library.
From this directory run

```sh
python3 checks/theta_example.py
python3 checks/field_example.py
python3 checks/prime_leakage.py --check checks/prime_leakage.json
```

- `theta_example.py` uses integer interval arithmetic to locate a zero of one
  Dedekind zeta function in the open height interval (1.20, 1.23) and to
  certify the other function is nonzero on the whole closed critical-line
  segment. Its expected output is in `theta_example.txt`.
- `field_example.py` checks an independent rational explicit-formula
  calculation for the same fields. Given the zero-line theorem and the
  cited zero-count estimate, their positive-height multiplicity discrepancy
  through height 80 totals at least seven. Its output is in `field_example.txt`.
- `prime_leakage.py` checks finite prime-power sums at nine combinations of
  scales and bandwidths and a quartic character modulo five. These calculations
  use ordinary floating-point arithmetic. The paper proves the uniform bounds
  analytically.

## Source revisions

- [Dirichlet GRH in Lean, readable edition](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
  The two relevant interfaces are `src/Statements.lean` and `src/Main.lean`.
- [ProveIt merged article](https://github.com/VladimirReshetnikov/ProveIt/tree/10802a6b360d5cdce48698261bc305e57a934b1f/Analysis/GeneralizedRiemannHypothesis/Article).
  In `sections/rec.tex` see `rec:cor:quadsep` and the question on the height
  needed for recovery. In `sections/zer.tex` see `zer:thm:short`.

The general bounds have absolute implied constants. Their numerical
optimization and a Lean formalization of the new arguments remain open.
