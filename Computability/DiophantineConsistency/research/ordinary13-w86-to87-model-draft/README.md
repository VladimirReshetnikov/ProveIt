# 86-to-87 w-coordinate model draft

This is an **unelaborated source-only proposal**, not a checked 86 bridge or
an iPRA endpoint. The exact 87 natural parent is generated from the pinned
forced-gamma JSON; the exact 86 literal is the separately generated
`EtaShifted86GraphDraft.literal`. Both use the same 13 input positions and
four natural compact ports, with K arbitrary.

The 87 parent defines `w=n_w+1`; the 86 child uses `n_w` directly. The
proposed `evaluation`/`zero_iff` sends a parent valuation to the 86 graph by
raising coordinate 6. The reverse map subtracts one from coordinate 6,
requiring that coordinate to be positive at the given 86 zero. No 85 eta
positivity is assumed for this edge.

`w_positive` proposes a direct reuse of the earlier 85 graph argument: an
actual 86 zero maps **forward** to an 85 prototype zero by raising coordinate
9; the 85 `EtaNaturalXPositiveDraft.witness_positive` then gives positive
coordinate 6, which the eta map leaves unchanged. This relies on the proposed
85/86 evaluation theorem and the exact prototype J/unit-factor/main-norm
proofs. It is not a circular use of the 85↔86 zero equivalence: only the
unconditional forward direction is used. Natural port K0 and positive
model-cast beta are inherited; the compact client obtains beta positivity
from the separate fixed-beta source. None of these source drafts has been
Lean elaborated or provided with a checked provider/axiom closure.

The proposed compact `SameNoZero` transports an **explicit assumption** of
`PolynomialBridge` for this exact 87 forced-gamma parent to the exact 86
literal. The final 85 native client still additionally assumes all-model
`ForcedEta K`; neither the 87 bridge nor eta forcing is proved here. The
remaining 87→88 gamma-forcing and earlier compact endpoint chain, fixed
external port/file/PDF interpretation and actual proof-theory axioms remain
open. No displayed equation is modified.

From `Computability/DiophantineConsistency`, run
`python3 -I -S -B research/ordinary13-w86-to87-model-draft/check.py` and compare
with `receipt.json`. This regenerates the 87 literal in a temporary tree,
checks both exact graph edits and bounded valuation identities; it does not
run Lean or establish arbitrary-model zero maps.
