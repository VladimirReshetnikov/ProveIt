# Finite strategy certificates for iPRA

A research note complementing existing ProveIt finite-witness frameworks.

- `report.tex` and `report.pdf`: human-readable proof schemas, applications, boundaries, and Lean migration plan.
- `lean/FiniteGameBlueprint.lean`: standalone Lean 4 source *blueprint*, not kernel verified; explicitly lists proof obligations.
- `code/finite_game.py`: executable exact finite-game strategy/counterstrategy construction and finite-contract reference tests.
- `verification/tests.txt`: recorded sample test result.

## How to run

```sh
python3 code/finite_game.py
pdflatex -interaction=nonstopmode report.tex
pdflatex -interaction=nonstopmode report.tex
```

## Status

The paper gives human proofs of the fixed-bounded-formula strategy compilation theorem and finite challenge decomposition. The Python program tests finite examples only. The Lean source contains definitions and an explicit formalization plan; it is not claimed to compile, and it does not construct `Prf PRAAx` terms. No general Faltings/Siegel result or global height/modulus theorem is claimed.

Primary upstream sources are linked in `report.tex`. No GitHub files were modified.
