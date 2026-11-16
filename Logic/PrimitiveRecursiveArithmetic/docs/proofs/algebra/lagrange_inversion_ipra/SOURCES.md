# Sources and exact snapshots

Access date: November 15, 2026.

## Primary target page

- Wikipedia, **Lagrange inversion theorem**, revision `1348379317`, last edited
  April 12, 2026:
  `https://en.wikipedia.org/w/index.php?title=Lagrange_inversion_theorem&oldid=1348379317`

## ProveIt

- Repository: `https://github.com/VladimirReshetnikov/ProveIt`
- Inspected `main` commit:
  `d1a012c54afe5612ab9e5fc7f4b38cf949648629`
- Key files/directories:
  - `lakefile.toml` - pins Mathlib `v4.32.0`.
  - `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
    - defines `PR`, `PTm`, `PRAAx`, `PRA.precZero`, `PRA.precSucc`, and
      `PRA.qfInd`.
  - `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean`
    - provides `pra_theorem_iff`.
  - `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/taylor_cauchy_ipra/report.tex`
    - constructive analytic-name, finite-list, and modulus conventions reused
      in the analytic lifting.

## Mathlib v4.32.0

- `Mathlib/RingTheory/PowerSeries/Substitution.lean`
- `Mathlib/RingTheory/PowerSeries/Derivative.lean`
- `Mathlib/RingTheory/PowerSeries/Inverse.lean`
- `Mathlib/RingTheory/PowerSeries/Exp.lean`
- `Mathlib/RingTheory/MvPowerSeries/Substitution.lean`

Versioned source root:
`https://github.com/leanprover-community/mathlib4/tree/v4.32.0`

## Mathematical references

- Ira M. Gessel, **Lagrange inversion**, JCTA 144 (2016), 212-249.
  `https://arxiv.org/abs/1609.05988`
- Erlang Surya and Lutz Warnke, **Lagrange Inversion Formula by Induction**,
  American Mathematical Monthly 130 (2023), 944-948.
  `https://arxiv.org/abs/2305.17576`
- Marcelo Aguiar and Federico Ardila, **Hopf Monoids and Generalized
  Permutahedra**, especially the polytopal compositional inversion theorem.
  `https://arxiv.org/abs/1709.07504`
- Robert M. Corless, David J. Jeffrey, and Donald E. Knuth,
  **A sequence of series for the Lambert W function**, ISSAC 1997.

## Source-use note

The paper does not copy a long passage from any source. It proves the formulas
independently and uses the source page only as the checklist of assertions to
address. The associahedron normalization was checked against the ordinary
coefficient convention in Aguiar-Ardila.
