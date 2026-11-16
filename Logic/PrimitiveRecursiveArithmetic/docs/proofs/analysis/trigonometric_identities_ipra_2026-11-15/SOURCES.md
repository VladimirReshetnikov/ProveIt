# Sources and inspected repository interfaces

Access date: 15 November 2026.

## Identity catalog

- Wikipedia, *List of trigonometric identities*:
  https://en.wikipedia.org/wiki/List_of_trigonometric_identities

The archive does not reproduce the Wikipedia page. `artifacts/coverage.csv`
records which families are proved, guarded, outlined, or left for a separate
analysis library.

## ProveIt interfaces reused

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected paths on the default branch:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  - file blob SHA: `3251631592070d9ed3687cc0bf7dbd5eb452e46f`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/EqArith.lean`
  - file blob SHA: `5d7b5b1f6710fb6c810e7f6ead1307c13a765ce4`
- `Analysis/TrigonometricIdentities/Lean/TrigonometricIdentities/ArctanSquareIdentity.lean`
  - file blob SHA: `3bf884aa2170918fc70794a4fe2aa69ff33c14e8`
- `Analysis/TrigonometricIdentities/Lean/TrigonometricIdentities/TrigGoldenRatio.lean`
  - file blob SHA: `d4b70889b12e17a2d94d6444e0fb76900cdffe97`

The existing `Analysis/TrigonometricIdentities` files use Mathlib's real
analysis. They were consulted for repository organization and proof style; the
new report instead specifies a direct constructive-real interpretation in iPRA.

## Constructive-analysis references

- Errett Bishop and Douglas Bridges, *Constructive Analysis*, Springer, 1985.
- Douglas Bridges and Fred Richman, *Varieties of Constructive Mathematics*,
  Cambridge University Press, 1987.
