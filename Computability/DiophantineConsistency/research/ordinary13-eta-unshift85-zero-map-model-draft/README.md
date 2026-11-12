# Conditional eta-unshift zero maps and native iPRA bridge

These are **unelaborated source drafts**, not a proved zero equivalence, a
proved eta-positivity theorem, or an end-to-end iPRA/ZFC result. The new
`EtaShifted86Graph` literal is generated from the exact 86-operation parent
JSON. The child is the separately generated exact 85-operation structural
prototype `EtaNaturalUnitGraphDraft.graph.output`.

`raiseEta` increments coordinate 9, and `lowerEta` takes its natural
predecessor. The intended polynomial evaluation identity is

```
parent(p,v) = child(p,raiseEta(v)).
```

Thus every parent zero maps forward by incrementing eta. In the reverse
direction the client assumes **for every IΣ₁ model** that a child zero has
`v 9>0`; only then may it take the predecessor and use `raiseEta(lowerEta v)=v`.
This `ForcedEta K` is an explicit premise, not a claim that the current
parity-boundary drafts have established it. The displayed evaluation proof
and all zero maps still require Lean elaboration; the 86 literal and the
85 graph must be supplied by compatible providers.

For an arbitrary natural K, both graphs use exactly
`Residue90CompactPortBoundsDraft.ports K`, including its fixed beta, K, low
and once-shifted high components. Under the same `ForcedEta K` and an
explicit `PolynomialBridge` for this exact 86 parent and tuple, the proposed
`SameNoZero` composition gives the child's `PolynomialBridge` and then an
internal `nativeTheory ⊢ nativeNoZero(child) ↔ ¬mappedNativeRefutation`
statement through the existing bridge API. The parent bridge is itself an
assumption; this packet does not identify or construct it, authenticate a
fixed K or external bytes/PDF, prove the mapped refutation is the user's
particular consistency formulation, or validate any iPRA theory adapter.
No literal proof-object in the target arithmetic is generated here.

The previous parity client still assumes represented strong/aux graph
identities, and all its source/provider/proof obligations remain. The
no-zero reflection, exact 86-to-earlier-parent bridge, compact tuple
provenance, theorem elaboration, actual `#print axioms` reports, and coherent
provider ancestry are separately open. `#print` lines here are unexecuted.
The existing displayed equation is not modified.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B research/ordinary13-eta-unshift85-zero-map-model-draft/check.py`
and compare with `receipt.json`. It independently regenerates the 86 literal
in a temporary tree, checks the exact graph substitution and finite valuation
controls, and does not run Lean.
