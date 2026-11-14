# Depth-budget history for a formula closer

`PA194FormulaBudget.lean` gives a candidate-PRA code `packedResult next` for
an arbitrary four-input stage update `next`. The history is indexed by a pair
of a source formula code and remaining depth budget; the selected label and a
fixed depth ceiling remain parameters. On an arbitrary candidate-PRA model,
`lookup_same` retrieves the output for a strictly smaller child at the same
budget, while `lookup_binder` retrieves it at one less budget. These results
assume certificates for the two history projections but do not assume IΣ₁.

The additional `all_body_lt`, `exs_body_lt`, and Boolean-child inequalities
instantiate the rank decrease for Foundation's internal formula constructors;
they assume an IΣ₁ arithmetic reduct, as required for these constructors. All
parameters may be nonstandard model elements. The printed results depend on
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

This is only generic recursion infrastructure: `next` is still an arbitrary
parameter. There is not yet an explicit formula-node update, a complete
candidate-PRA formula-closing code, its constructor equations, or a proof that
changing the fixed ceiling leaves results invariant. In particular this file
does not establish formula translation correctness or the machine/refutation
equivalence. Run `check-formula-budget.sh` with the audited
`IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY` set.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local prerequisites and checking the displayed axioms for `sorryAx`.
