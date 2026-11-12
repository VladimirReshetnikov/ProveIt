# AQ17/105 mixed-shift transfer and forcing draft

This packet transcribes the 17-natural-input, 105-operation graph and its
eight residuals to inert Lean source. It proposes a modular no-zero transfer
to the fully positive-shifted AQ17/94 expression. **Nothing here has been
elaborated or kernel-checked**, and the proposed native and standard endpoints
remain explicitly conditional on graph-evaluation and forcing assumptions as
well as all inherited AQ17, AQ20 and AQ22 graph obligations.

The valuation `mixed` leaves indices `3, 5, 11, 14, 15, 16` unchanged (`f`,
`T`, `y`, both quotients and `vValueVariable`) and adds one to the other 11.
The `ZeroEquivalence` hypothesis says that the exact 105-row literal vanishes
iff the positive parent vanishes on that mixed valuation, for every signed
port tuple and every ordered IΣ₁ model used here. The `SixForced` hypothesis
says each of the six natural coordinates is positive at a child zero. Given
those hypotheses, the source proposes both directions of no-zero equivalence
by adding or subtracting one in the appropriate coordinates.

The separate arithmetic draft proposes lemmas that obtain positivity from
precise arithmetic cuts: the two quotient norm equations, the strong and
auxiliary equations, the reconstructed time binding, and the signed `f`
expression. `ForcingCut` states those six coordinate facts together, and
`sixForced_of_cut` proposes their assembly. **Graph-to-cut extraction remains
an explicit unproved premise**, including construction of the represented
natural `q`, the bound `q ≥ 4`, and the displayed auxiliary and time equations.
The external graph checker establishes exact finite polynomial identities,
not those model facts or the Lean proof.

The optional `j_pos_of_root_branch` is a separate arithmetic proposal for the
seventh shift in [AQ17/104](../adaptive-aq17-natural-forced104/). It explicitly
requires the signed second port's image to equal `ι k` for some model-natural
`k`, plus the exact zero-branch root equation and positive `f`. Extracting that
branch from AQ17/104 and connecting the fixed second port via
`ModelThirteenCarrier.port1` are **not** provided here. The previously
inherited AQ20 transfer separately needs strict positivity and representation
of the first port. Neither claim extends automatically to arbitrary negative
second ports.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B research/adaptive-aq17-forced105-model-draft/check.py | cmp - research/adaptive-aq17-forced105-model-draft/receipt.json
```

The read-only checker pins the finite graph, sources and inherited draft
receipts; checks residual-vector arity and forced-coordinate mapping; and
reruns the graph author's checker. It does not execute Lean, validate the
arithmetic tactics, authenticate providers or establish an iPRA endpoint.
