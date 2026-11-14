# Closing shift-fixed syntax and induction axioms

`PA194ShiftFixedClose.lean` proves that if an internally well-formed arithmetic
term is unchanged by Foundation's free-variable shift, then closing any label
at its well-formedness depth leaves the term unchanged. It proves the analogous
statement for an internally well-formed formula, at any model-valued label
and depth, by internal structural induction. These are implications with an
explicit shift-fixed premise; they do not assert that arbitrary formulas are
shift-fixed.

For every code accepted by Foundation's concrete `InductionUnivR` recognizer,
including nonstandard codes and a nonstandard number of universal binders,
`induction_axiom_close_fixed` proves closing any label at depth zero leaves
the code unchanged. The recognizer requires the unquantified body to be
shift-fixed; the proof lifts this through all internal universal binders and
checks the resulting formula is well formed at depth zero.

The theorems hold in every nonempty candidate-PRA model with equality and an
IΣ₁ arithmetic reduct. Lean reports only `propext`, `Classical.choice`, and
`Quot.sound` for the printed theorem dependencies. They do **not** establish
invariance under arbitrary free-variable renaming, invariance of all PA axioms
(the finite Peano-minus branch is not covered), a proof-renaming transformer,
or either PA194 consistency implication.

Run `check-shift-fixed-close.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set. It rebuilds the closer dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local formula-closing prerequisites and checking the theorem dependencies
for `sorryAx`.
