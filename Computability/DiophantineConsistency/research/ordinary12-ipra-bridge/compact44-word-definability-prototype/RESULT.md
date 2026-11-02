# Exploratory word-lookup composition definability

`CompactWordDefinability.forward_composition` and `.inverse_composition` state that, for any `IΣ₁` model, composing a supplied Σ₁-definable model word with the exact forward row lookup or exact inverse row lookup is Σ₁-definable. The proof promotes the relevant Σ₀ lookup instances to Σ₁ and uses the project's definability tactic.

Author-only session 33084 actually exited 0 without warnings or `sorryAx`. Both named axiom reports were `[propext, Classical.choice, Quot.sound]`. It used `/tmp/compact-reverse-explore-01/lib`, the same-provider exploratory reverse-chain overlay described in commit `66d55d623b`; no compiler object or raw transcript for this small client was retained. This is not a paired replay or independent artifact audit.

This result is conditional on a supplied Σ₁-definable function and does not construct a word or tableau, establish matching or wrap, prove a paired reverse bridge, calibrate the compact checker, or prove a 12-variable iPRA endpoint. Lean metatheory reports are distinct from the encoded object theory's axioms.
