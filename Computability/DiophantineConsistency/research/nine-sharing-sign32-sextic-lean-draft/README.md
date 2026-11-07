# Sign32 sextic: Lean syntax and bridge draft

This packet is **source only**. No Lean invocation, elaboration, or theorem check has been performed here. In particular, neither zero-set direction is proved. The candidate is a 32-witness, degree-six seed; the existing nine-variable Jones reduction requires degree at most four and does not apply to it. This packet establishes no new endpoint.

`generate.py` generates `SharingSeed32Sextic.lean` from the independently reviewed `../nine-sharing-sign32-sextic-candidate-v2/seed.json`. The independent `check.py` parses the generated source's restricted expression syntax and compares all 23 residual ASTs against that JSON; it reports maximum residual syntactic degree three. `result.json` records the source-only check. This external parser comparison does not provide a Lean-verified JSON semantics, numeric model-port binding, or a proof that the generated source elaborates. `NineFreshJones` is imported for existing syntax support, not to claim the quartic reduction applies.

`SharingSeed32BridgeDraft.lean` proposes a natural-model lift, a drop, and two **open propositions** `ForwardTarget` and `BackwardTarget`. Full coordinate zero is the distinguished input; `Fin 33` comprises that coordinate plus 32 witnesses, while `Fin 34` comprises it plus 33 witnesses. The lift preserves coordinates 0–14, inserts `(beta * (v 1 + 1) + 1)^2` at full coordinate 15, and moves new coordinates 15–32 to old coordinates 16–33. The drop removes old coordinate 15. Both propositions require the explicit equality between port 0 in the model difference ring and the image of the natural-model `beta`. The other ports remain symbolic. `check_bridge.py` records a source-text mapping check in `bridge-result.json`; it does not parse or run Lean.

A forward proof still needs a sum-of-squares zero decomposition in the model, substitution identities for the 23 residuals, and the natural-to-difference-ring homomorphism facts. A backward proof additionally needs the old eliminated residual, injectivity of the natural embedding to recover coordinate 15, and the reverse substitution identities. The current-source coefficient/high-port binding is separate. Any eventual semantic bridge and bounded batches require actual Lean checking and provider authentication.

Reproduce the source checks from the repository root (no Lean):

```sh
python3 research/nine-sharing-sign32-sextic-lean-draft/generate.py
python3 research/nine-sharing-sign32-sextic-lean-draft/check.py
python3 research/nine-sharing-sign32-sextic-lean-draft/check_bridge.py
```

Running these scripts rewrites generated files or results, so preserve the frozen packet and compare against a temporary copy when independently replaying.

The [independent source audit](../../reviews/nine-sharing-sign32-sextic-lean-frontier-independent/README.md) passed, including separate AST parsing and temporary replay. Read [ERRATUM.md](ERRATUM.md) and [ERRATUM-ADDENDUM.md](ERRATUM-ADDENDUM.md) for the corrected replay commands and generated-output precondition.
