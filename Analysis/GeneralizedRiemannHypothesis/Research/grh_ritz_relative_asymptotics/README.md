# Exact relative error laws for Li moment pencils

Research packet, 27 November 2026.

- `research.tex`, `research.pdf`: complete 11-page proof and discussion. The abstract theorem is unconditional; arithmetic applications take the supplied RH/Dirichlet GRH theorem as input.
- `experiment.py`, `experiment.csv`, `experiment.log`: high-precision illustration using moments from Taylor data of the completed zeta function, not input zero ordinates.
- `experiment_repeat.csv`, `experiment_repeat.log`: independent higher-precision repeat using the same algorithm. The CSV files match byte for byte. These are numerical checks, not rigorous interval computations.
- `exact_checks.py`, `exact_checks.log`: rational finite-measure verification of the residual identity and inequalities for two ranks, up to correction order three.
- `SOURCE_NOTES.md`: inspected source paths and exact blob identifiers.
- `FORMALIZATION.md`: proposed formalization dependency map, not a Lean implementation.

## Reproduce

```sh
pdflatex -halt-on-error -interaction=nonstopmode research.tex
pdflatex -halt-on-error -interaction=nonstopmode research.tex
python -m pip install mpmath==1.3.0
python experiment.py > experiment.log
python experiment.py --dps 140 --samples 512 --output experiment_repeat.csv > experiment_repeat.log
cmp experiment.csv experiment_repeat.csv
python exact_checks.py
```

The code uses Python 3 and mpmath. The proof is independent of the code. The input theorem was inspected via GitHub, not locally rebuilt. No attempt was made to modify the upstream repository. The worldwide novelty of the results has not been certified; the new formulas are a substantive extension of the inspected `li.tex` statements. The absolute next coefficient of the Ritz error remains unresolved.
