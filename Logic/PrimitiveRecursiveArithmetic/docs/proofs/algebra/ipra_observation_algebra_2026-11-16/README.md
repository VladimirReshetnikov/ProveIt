# Branch-free finite observation algebra for iPRA

Research note (2026-11-16). Start with `paper/main.pdf`, source in `paper/main.tex`.

## Claim boundary

* Developed conventional mathematical arguments: monic finite-algebra normal form, matrix observation and resultant representation, substitution/quotient functoriality, Newton identities without division, conditional stability, and a concrete branch-free Puiseux-family workaround.
* Exact rational reference implementation and tests: `code/observe.py`, `code/test_observe.py`.
* Lean: `lean/ObservationBlueprint.lean` is a *noncompiled blueprint* with basic definitions and an explicit path to object-language derivations. It is **not** a finished `Prf PRAAx` formalization.
* Neither general Puiseux branch selection from arbitrary Cauchy names nor general Faltings/Siegel height bounds are claimed.

## Reproduce

`cd code && python3 -m unittest -v test_observe.py`

`cd paper && pdflatex -interaction=nonstopmode -halt-on-error main.tex`

## Repository references

See bibliography and direct links in `paper/main.tex`. The source repository was read-only; no changes were pushed.
