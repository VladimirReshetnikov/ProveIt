# Internal PA preserves the numerical source universal rule

`PA194SourceUniversalPreservation.lean` proves, in every nonempty
candidate-PRA model with equality and an IΣ₁ arithmetic reduct, that internal
PA provability of the positive translation of a numerical source body implies
internal PA provability of the positive translation of its universal
conclusion. Both the body code and quantified label may be arbitrary model
values, including nonstandard ones. This removes the extra reopened-body
provability premise from `PA194SourceAllPreservation.all_of_free` at the
model-uniform level.

The proof identifies the initial expanded-map formula traversal with
Foundation's `free (close label 0 φ)` for every internally well-formed,
including nonstandard, formula. To handle internal binder depth, it uses an
opening-vector invariant that is preserved by `qVec`; structural induction
then proves the equality for arbitrary depth. The prior model-internal
PA-derivation renaming theorem supplies a derivation of that reopened formula
from a derivation of `φ`. The existing conditional source-rule theorem then
yields the universal conclusion.

The printed theorem dependencies are `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. This proves a model-uniform existence
statement about internal PA proofs. It does not exhibit a fixed
primitive-recursive proof-code transformer, establish an object-theory iPRA
theorem, prove preservation of complete numerical source derivations, or prove
either PA194 machine/consistency implication. Those remain separate steps.

Run `check-source-universal-preservation.sh` with the audited
`IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY` set; it rebuilds both the
renaming and source-translation dependencies in a fresh temporary overlay and
rejects `sorryAx`.

An independent suffix replay recompiled this module against the independently
checked final derivation-renaming module and retained prerequisite overlays.
The reported theorem axioms did not include `sorryAx`. An independent full
`check-source-line-soundness.sh` replay also rebuilt this theorem and its
combined dependencies without `sorryAx`.
