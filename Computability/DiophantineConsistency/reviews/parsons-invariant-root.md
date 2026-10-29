# Marked-context invariant for the cut-free reduction

`ParsonsInvariant.Entry` records each sequent occurrence separately as a
Π₂ side formula, an actual PA-minus axiom with membership certificate, or a
Σ₁ induction formula with a certified partially opened parameter-block state.
The entry's original formula and its side contribution are separate: base
and block entries contribute falsity, while side entries contribute their
formula. `output_pi_two` proves the resulting finite side disjunction is Π₂
in Foundation's non-prenex hierarchy.

`initial` marks the actual output of `ParsonsTheoryNormalize` when the
conclusion has a Π₂ certificate. `initial_formulas` identifies the marked
formulas with the exact normalized sequent, and `initial_derivation` retains
its actual cut-free derivation. `initial_result` turns a rule proof of the
marked output into a rule proof of the original conclusion. It does not
provide that missing output proof.

`base_branch` proves the complete marked case with no induction blocks,
including arbitrarily interleaved sides and PA-minus axioms. For contraction,
`selectEntries` chooses a marked occurrence for each formula in the premise;
`selected_formulas` and `selected_outputs_subset` verify the selection, even
if equal formulas have different tags. `marked_contraction` applies the local
recursive hypothesis to the actual cut-free premise at strictly smaller
height and transports its output proof to the conclusion. Choice is used in
selecting occurrences; the choice need not be computational.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Eight
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The [16-file replay manifest](parsons-invariant-replay/FILES.json) has SHA-256
`c0d05be4f305776c61d303bd0e04ce3d20419722c74dba204974231e70950c3f`.
Direct `ParsonsBlock` source/object hashes are
`fe4b12db6a838a20a7b0bc0b091c6358ab7b8416344bd1b14008205304e597fb` /
`de34b949427330052959dcf41a44770253d20f8a7f41fb27cae77a3a09e24fde`;
`ParsonsFold` hashes are
`c176115407aabd79ea2e39ade1a3818f5d0233a7dba15253eb4b66b16a61d402` /
`9396383c58f41461c56e470afdbf159ed30c31ac389b8a538d193a7ec32f4411`.
Both current provider sources match their frozen snapshots. Prior providers,
Foundation/Mathlib, and completeness objects remain an inherited boundary,
not a fresh transitive audit. An exploratory initial-constructor elaboration
hit the heartbeat limit; breaking it into a helper fixed the source.

This is an initialized invariant and two proved cases, not the global
strong induction. Nonprincipal and principal logical cases must be integrated
with the marked Π₂ side context, and the principal induction block still
requires an adapter that exposes a Σ₁ guard from that context. Π₂ hierarchy
membership alone does not supply such a strict prenex form. No overall
conservation theorem or PRA proof is asserted.

## Independent root replay

A third build at `/tmp/parsons-invariant-build-wc17j1di` passed; its source,
object and complete-log hashes match both author builds. The fold provider
matches the independently rebuilt object. The [independent artifacts](parsons-invariant-replay/root-build/)
are preserved; the Foundation/Mathlib boundary remains inherited.
