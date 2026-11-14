# Conditional source universal-generalization step

`PA194SourceAllPreservation.lean` fixes the previously certified source and
formula-closer codes. `universal_code` proves, for all model-valued source
bodies and labels, that the positive translation of a numerical universal
constructor is Foundation's internal universal constructor applied to the
internally closed positive translation of the body. The previous source-output
well-formedness theorem discharges the recursive well-formedness conditions.

`all_of_free` proves a **conditional** model-internal PA-provability step:
if PA internally proves Foundation's `free` reopening of that closed body,
then PA internally proves the positive translation of the universal
conclusion. Both results hold for arbitrary, including nonstandard, values in
every nonempty candidate-PRA model with an IΣ₁ arithmetic reduct and equality
interpreted as equality. There are no extra decoder-certificate premises.
The printed axiom dependencies are `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

The source rule instead starts with a proof of the original translated body.
This package does **not** derive the reopened-body premise from that proof.
Reopening renames the selected free label to zero and sends every other free
label to its successor. A model-internal proof-renaming transformation, with
quantifier/eigenvariable and the proof calculus's explicit shift-rule cases,
remains required. Consequently this package does not prove unconditional
source generalization, preservation of whole derivations, an iPRA theorem,
or either machine/consistency implication.

Run `check-source-all-conditional.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; the script rebuilds the relevant source
translation and polarity dependencies in a fresh temporary overlay.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the relevant source translation and polarity dependencies. The displayed
conditional theorems did not depend on `sorryAx`.
