# Reopening the internal PA axiom class

`PA194PAAxiomReopen.lean` proves that every model-internal code `p` accepted
by Foundation's concrete `𝗣𝗔.Δ₁Class` satisfies

```
free ℒₒᵣ (PA194InternalFormulaClose.close label 0 p) = p.
```

The label and `p` may be nonstandard. The proof inspects the exact chosen
PA recognizer: its induction component is handled by the predecessor
`PA194InductionAxiomReopen`; for its finite Peano-minus component, a lemma
shows the finite-list recognizer contains exactly the quoted standard sentences
from that list in every model. A standard sentence's quoted code is shift-fixed
and well formed, so the predecessor's close and reopen lemmas apply.

This holds in every nonempty candidate-PRA model with equality and an IΣ₁
arithmetic reduct. Lean reports `propext`, `Classical.choice`, and `Quot.sound`
for the printed dependencies, with no `sorryAx`. The theorem concerns the
specific close/reopen operation; arbitrary protected-prefix renamings,
derivation preservation, an iPRA proof, and the PA194 consistency equivalence
remain open.

Run `check-pa-axiom-reopen.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent fresh Linux replay passed using the audited overlays, including
the local dependency rebuild. The reported axiom-class theorem did not depend
on `sorryAx`.
