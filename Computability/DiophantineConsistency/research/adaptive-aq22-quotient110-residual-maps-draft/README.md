# AQ22/110 residual-map proof draft

This is a proposed **unelaborated** Lean discharge of the two graph-zero
obligations in [the model-transfer draft](../adaptive-aq22-quotient110-model-draft/).
No Lean theorem, tactic, import, or axiom report in this packet has been
checked, and the historical parent provider closure has not been replayed.

The source states and attempts to prove all 13 pointwise residual comparisons
in the model difference ring after extending a child valuation. For indices 0
and 1, the parent residual is the child residual multiplied by the square of
its scale; indices 2–12 agree. The corresponding Python graph checker proves
the finite polynomial identities independently; it does **not** validate the
Lean proofs or the model interpretations. `extend_zero` applies the 13
identities to a child zero. `project_zero` reconstructs the old valuation from
its two quotient equations and uses the quotient norm equations for the first
two residuals. The source then proposes a term for `GraphZeroObligations`
and a closed native client; the latter relies on the unelaborated quotient
extraction and conditional bridge in the prior packet.

Extraction of the positive quotients is in the prior packet and invokes
`ArithmeticAdaptiveQuotients2011.scaled_quotient` twice. It requires positive
parent scales and roots, supplied for positive-shifted witnesses. The local
graph maps work for arbitrary signed ports; the fixed current ports appear
only in the final conditional bridge. The separate 132-operation natural JSON
is not Lean-proved equal to `positiveShift child`. The parent AQ22 endpoint
has a historical paired replay, which does not constitute a replay of these
new sources or proof of equivalence to an untranslated consistency sentence.

Run the bounded, read-only check from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive-aq22-quotient110-residual-maps-draft/check.py | cmp - research/adaptive-aq22-quotient110-residual-maps-draft/receipt.json
```

This checks pinned source bytes, all residual declarations/case coverage and
the graph author's reproducible polynomial receipt. It performs no Lean run,
staging, compiled-provider authentication or kernel verification.
