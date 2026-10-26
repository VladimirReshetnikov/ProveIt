# Release manuscript and artifact audit

Prepared 26 October 2026 by the separately assigned quartic research agent.
The audited release is `ConZFC_Pell_Growth_210_2026-10-25`.

The principal 210-variable data and all direct-construction complexity claims
in `report/main.tex` agree with independent exact expansion. The same is now
verified for the balanced 214-variable companion. The principal chain uses
79 elementary integral operations; the balanced chain uses 75. Their final
metrics are respectively `(210,150,4,5282,1099511627776)` and
`(214,153,4,5699,91679)`, ordered as variables, residuals, degree, monomials,
and coefficient height.

The manuscript's new Pell growth, delayed sign recovery, affine radix,
finite binary-residue lifting, and prime-support beta-CRT proofs are
consistent with the literal source mutations and with the independent
review. In particular, the proved growth target is
`F >= (8^(2^19-1)*t^(2^19))^t`, not the old stronger exact-power condition.
The manuscript correctly acknowledges the retained logical calibration and
the absence of a fresh complete proof-assistant build.

Two presentation corrections were reported to the coordinating agent:

1. The anchor-cap display initially omitted the backslash in `\quad`.
   The current inspected manuscript has this corrected.
2. The separate affine-radix proof note said there were two lower cutoffs.
   The actual three are `t`, `y+1`, and `x`. The proof's uniform inequality
   already includes the last case. The owned source note has been corrected
   so the package can copy the corrected version. The manuscript itself
   already gives all three cutoffs correctly.

No further numerical or algebraic discrepancy was found in the inspected
direct-construction sections. The compact positive-domain companion is
outside this agent's assigned independent verification scope and is reviewed
by its separate assigned researcher. PDF rendering and the final master
rebuild are also handled separately.
