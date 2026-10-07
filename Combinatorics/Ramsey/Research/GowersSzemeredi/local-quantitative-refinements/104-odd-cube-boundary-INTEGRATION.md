# Integration notes

A proposed standalone destination is:

`Combinatorics/Ramsey/Research/GowersSzemeredi/odd-order-cube-stability/`

Alternatively, assign the article a new source number in the existing
`local-quantitative-refinements` collection. Do not overwrite or renumber source
101: this manuscript cites and extends it.

All new LaTeX labels use the prefix `ocb:`. The source is self-contained and uses
an embedded bibliography. Integration into a collected volume should preserve
its theorem hypotheses and distinguish the two torsion assumptions:

1. The cubic complement/profile requires the nearby subgroup H to have odd order.
2. The boundary and higher-dimensional profile require (G/H)[2] = {0}; H itself
   need not have odd order.

The main cross-reference is the affirmative solution of Conjecture 12.1 in the
earlier `sharp_cube_stability.tex` paper. Record the sharp boundary coefficient
2k with its explicit ratio restriction. The optimal ratio endpoint is still open.
The inverse boundary theorem here is for odd quotients, not arbitrary torsion.

The cubic energy remainder (12h-140r) Delta_E(R) is not claimed to dominate every
energy-sensitive remainder in the predecessor term-by-term. Its purpose is to
supply a nonnegative remainder while removing the 35 delta^4 loss from the scalar
profile. The exact occupancy identity permits retaining stronger data.

Keep the source audit and proof status with the paper. Do not mark any declaration
as Lean-checked and do not change `gowers-proof-status.json` or a formalization
ledger solely on the basis of this package. A separate checked formalization is
outlined in `FORMALIZATION_PLAN.md`.

`build/` and `_renders/` are local working directories, not distribution inputs.
Generated verification receipts are small and useful to retain. The supplied
SHA256 manifest identifies the delivered files; regenerate it after edits.
