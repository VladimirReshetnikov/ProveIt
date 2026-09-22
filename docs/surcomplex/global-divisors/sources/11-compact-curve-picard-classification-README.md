# Compact-Curve Geometry over Surcomplex Hahn Fields

**Picard classification, valuation monodromy, finite cohomology models,
and an exact Abel criterion**

Research manuscript prepared for Vladimir Reshetnikov with ChatGPT,
21 September 2026.

## Contents

- `article.tex`: standalone LaTeX source with internal bibliography.
- `article.pdf`: compiled article.
- `verification.py`: exact finite symbolic checks (Python 3.10+ and SymPy).
- `verification_results.json`: output of the recorded execution.
- `Makefile`: build and clean commands.
- `requirements.txt`: the recorded SymPy dependency version.
- `BUILD_REPORT.md`: build and verification summary.
- `research_scope.md`: literature and repository scope audit.

## Main results

1. An exact classification of locally free rank-one modules on a compact
   ordinary complex curve with common-domain Hahn coefficient sheaf.
2. Valuation monodromy is exactly the obstruction to a nonzero coherent
   meromorphic section; divisor classes occupy the zero-valuation sector.
3. A finite, support-controlled two-term cohomology complex in that sector,
   including Riemann–Roch and integral torsion information.
4. A root-free if-and-only-if Abel criterion for finite moving clusters,
   with an explicit nonlinear genus-two obstruction.
5. The exact kernel and target of all one-scale integral Picard
   truncations, including nontrivial deformations invisible modulo every t^n.

## Precise scope

The base is a compact connected **ordinary** Riemann surface. The
coefficient field is a set-sized Hahn field C((t^Gamma)) embedded in No[i].
All coefficient germs share an ordinary domain locally. No infinite sum
is interpreted as convergence in the fine topology of the full surreal
or surcomplex class. The integral quotient sheaf is used for truncations;
the corresponding quotient of the full Hahn field sheaf would be zero.

`Pic_lf` means locally free rank-one sheaves. The manuscript does not rely
on an identification with a larger invertible-module category, nor with
algebraic, rigid-analytic, Berkovich, or logarithmic Picard functors.

## Status

The stated results are accompanied by proofs in the defined category.
They are proposed research contributions, not certified first-in-literature
claims, and no named published conjecture is claimed resolved.
Classical Hahn algebra, Hodge and Picard theory, Riemann–Roch, Abel/Serre
duality, and homological perturbation are credited as foundations.
No independent referee report or proof-assistant verification is available.
Finite symbolic checks are not substitutes for the proofs.

The repository was inspected at commit:
`aa846271b4dcae2c055b216126a87210292ec19b`.
No changes were made to the remote repository.

## Reproduction

```sh
python verification.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded symbolic execution passed 53/53 exact checks. No numerical
randomness or tolerances are involved. Alternatively run `make`.
`make clean` removes LaTeX intermediate files but preserves the PDF.
