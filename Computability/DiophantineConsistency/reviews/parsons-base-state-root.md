# Tracking negative base theorems through principal rules

`ParsonsBaseState.BaseState` tracks a positive Π₂ theorem together with actual
PA-minus rule proofs of all its free-variable rewrites; the corresponding
sequent occurrence is its negation. `ofAxiom` initializes the state from an
actual PA-minus axiom and an explicit Π₂ certificate. `openState` handles a
principal negative universal: it specializes the positive theorem at the
actual existential witness, preserves Π₂ classification, and constructs the
whole family of rewritten proofs for the resulting open instance. `open_case`
uses the resulting state and a strictly smaller cut-free premise. `shiftState`
proves the family remains valid under an eigenvariable shift.

When the positive instance is Σ₁, `terminal` classifies its negation as a Π₂
side and `terminal_case` removes it using the actual positive rule proof and
resolution. That reclassification does not reduce derivation height, so a
single global strong induction needs a suitable secondary measure. The module
does not assert that every PA-minus axiom has the required initial Π₂ certificate
or that all of its open instances eventually have the required terminal Σ₁
shape; those are separate obligations.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Nine
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-base-state-replay/FILES.json) has SHA-256
`30127ec531f8ad6e66023cb7646e175e0ebcc3b2951c6cf7519c3e0152122d48`.
The direct `ParsonsInvariant` provider and its prior chain are recorded in
[its receipt](parsons-invariant-root.md); Foundation/Mathlib and completeness
objects remain an inherited boundary rather than a fresh transitive audit.
Scratch failures around rewrite notation and the quantified shift were fixed;
their console logs were not retained.

This is a candidate state and proved transitions for the negative-base case,
not yet integrated into the marked context. The full base-axiom shape proof,
all marked logical cases with this state, Π₂ guard opening, global induction,
and PRA witnessing remain open.

## Independent root replay

A third build at `/tmp/parsons-base-state-build-xmgh86d3` passed; source,
object and complete-log hashes match both author runs. The invariant provider
matches the independently rebuilt object. The [independent artifacts](parsons-base-state-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary.
