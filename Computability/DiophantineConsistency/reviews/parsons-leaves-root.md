# Identity and truth leaves of the unified recursion

`ParsonsLeaves.block_has_exists` proves that every certified induction-block
occurrence has an existential top constructor. This covers both unopened
parameter blocks and the fully opened state, where the stored state recovers
the existential counterexample matrix. Consequently a block cannot occur in
the exact atomic identity sequent or the singleton truth sequent.

`identity_leaf` and `verum_leaf` use that fact to call the unified base-only
branch. They construct actual PA-minus rule proofs of the marked side output,
including any shaped base entries, without local recursive hypotheses. These
are the two leaf constructors of Foundation's cut-free LK derivation type.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Six
axiom reports use no axioms beyond `propext`, `Classical.choice`, and
`Quot.sound`; the bare nonempty closure identity uses none. The
[16-file replay manifest](parsons-leaves-replay/FILES.json) has SHA-256
`6ddfb6d2db648bd782107a0b7568c5171a15b697f7aa77e08099a3116de9ef07`.
The direct `ParsonsUnified` source hash
`5683bd12a9012bdb1f904b8e8d1a1597b399143db8952f28d311c8ac390df6a6`
matches its frozen snapshot, and its object hash is
`dd078b2bea3f2d1fb2dc47529644ff38341fa1b317442b941a2b3dce2e5c4d44`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive audit. Scratch failures around
namespace notation and list membership were corrected; their logs were not
retained.

This closes identity and truth leaf analysis, not the global strong induction.
The final induction counter-witness still needs a Σ₁ guard, while the marked
side currently has only a non-prenex Π₂ certificate. Full Π₂ guard opening,
case dispatch, global well-founded recursion, and PRA witnessing remain open.

## Independent root replay

A third build at `/tmp/parsons-leaves-build-3lrhkcsh` passed; source, object
and complete-log hashes match both author runs. The unified provider matches
the independently rebuilt object. The [independent artifacts](parsons-leaves-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary.
