# Global cut-free recursion for the strict marked invariant

`ParsonsGlobalStrict.translate` proves in Lean, without an assumed recursion
hypothesis, that every cut-free marked derivation whose context is `Stable`
yields an actual `ParsonsRule.Proof 𝗣𝗔⁻` of its projected side disjunction.
`Stable` requires every ordinary side to carry a positive Boolean Tree
descriptor, every induction block to use a strict finite existential prefix
over a Σ₀ matrix, and every base state to carry the actual PA-minus
positive-prefix certificate.

The proof is a well-founded nested induction: derivation height is primary,
and base-state count is secondary for the same-height terminal
reclassification. It covers identity and truth leaves, contraction,
ordinary ∨/∧/∀/∃ rules, base-state opening and terminal discharge, and both
parameter-opening and final counterexample induction-block cases. The
counterexample case uses the previously established structural recursion over
Tree sides; all three invariant conditions are preserved.

This theorem is restricted to contexts satisfying the displayed invariant.
It does not show that arbitrary Foundation Σ₁ induction predicates are strict,
that every Π₂ conclusion has a Tree descriptor, or that the intermediate rule
calculus is candidate PRA. The separate HA result for the 14-variable PDF
equation is outside the scope of this theorem.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The four
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorryAx` is reported. The [16-file replay manifest](parsons-global-strict-replay/FILES.json)
has SHA-256 `9ea5cb7608fd692e84d7408248947a0865ae9c6ad71efc1f3f505c567d95d367`.
Direct provider hashes are:

- CounterStable source `98e3dfc71f5c8a7186dc0d0f1cedd29a8781fffdd4ab0678d93d1403d344711f`, object `37c1b693340701789d97db46b45e55dcc82fb0a3e74a2e84ab6390572487a0bd`.
- TreeLogical source `c3a04e5f1f853354fb5b4c24d92b38b1c3765e1bd65460e2d400512f2597f35c`, object `c46189285f8d39933e5c2ae1d0ee8a215c3d166cdd6bba325ef91228760f0167`.

Both direct sources match their frozen snapshots. Earlier provider chains,
Foundation/Mathlib, and completeness objects are an inherited boundary, not a
fresh transitive source audit.

A third independent replay at `/tmp/parsons-global-strict-build-vbbxtzh0`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
