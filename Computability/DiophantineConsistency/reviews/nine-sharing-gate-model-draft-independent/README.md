# Independent source-only review of the gate-model draft

`check.py` independently parses both uncompiled semiring constructors and
compares their abstract syntax to the pinned 52- and 54-witness seed JSONs.
All 38 and 40 cut assignments respectively match in sequence, read only
previously defined coordinates, and the output vectors preserve the 14 input
coordinates followed by the cut coordinates. Port indices 0, 1, 2, 3 denote
beta, K0, MC, MF. The input-output residual itself is not checked by this
constructor comparison. The result pins each reviewed Lean file and JSON.

Inspection of the separately pinned `SharingGateModel.lean` found the usual
signed-pair operations and algebraically valid candidate identities: each
pair represents the difference of its two semiring images; addition,
subtraction and multiplication preserve this representation; vanishing
component residuals imply the represented gate value; and the proposed
reverse replay explicitly assumes a full chronological `ResidualTrace`.
One-component replay additionally assumes the computed negative component is
zero **in the semiring**, not merely after mapping into the ring. A graph with
inlined gates and one final witness assignment still needs a Lean construction
of the chronological trace and a connection to its source expression.

This is a syntax and mathematical inspection, not a Lean elaboration, kernel
check, provider-closure check, fixed-port image proof, model bridge, or iPRA
endpoint. `SharingGateModel` imports `NineFreshJones`; its import resolution and
the tactic scripts are untested here. In particular, typeclass inference,
`Function.update` rewrites and induction elaboration remain proof risks. The
author's original checker and README described only the 54 constructor; the
author subsequently updated those files and the recorded result to cover both
constructors. The Lean sources and seed JSONs were unchanged by that update.
This review independently compares both source variants.

Run `python3 -I -S -B check.py` to reproduce the syntax comparison. No Lean
process was run.
