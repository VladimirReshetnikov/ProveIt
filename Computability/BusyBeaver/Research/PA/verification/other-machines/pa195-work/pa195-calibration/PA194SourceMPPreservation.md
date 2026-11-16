# Model-internal preservation of source modus ponens

`PA194SourceMPPreservation.lean` proves that the explicit fixed named-source
translation preserves the PA194 numerical calculus's modus-ponens rule with
respect to Foundation's **internal PA-provability predicate**. In every
nonempty candidate-PRA model with an IΣ₁ arithmetic reduct and equality
interpreted as equality, for arbitrary model elements `a` and `b`:

* if PA internally proves the positive translation of `a`, and
* PA internally proves the positive translation of `I(a,b) = 4 * cantor a b`,

then PA internally proves the positive translation of `b`. The source codes
and the witnesses to internal PA provability can be nonstandard model
elements. The source tag and child decoders and the formula-closer projections
are the previously fixed certified codes, so the theorem has no additional
certificate premises.

For nonzero implication codes, `implication_code` identifies the translated
positive formula with Foundation's internal implication of the two translated
positive formulas. The proof uses all-model output well-formedness, syntactic
polarity, and Foundation's internal typed derivation rules. The exceptional
source alias `I(0,0) = 0` is handled separately: `implication_zero` proves
that a zero implication code forces both source inputs to be zero, after
which the conclusion is the first premise. Lean reports only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`, for the results.

This is an all-model implication between internal *existence* predicates for
PA proof codes. It is not yet an explicit primitive-recursive transformer from
particular premise proof codes to a conclusion proof code, nor an object-theory
PRA/iPRA derivation. It proves no source generalization or axiom preservation,
no translation of whole derivations, and neither PA194 machine/consistency
implication.

Run `check-source-mp-preservation.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set. The script rebuilds the formula closer, source
translation, well-formedness and polarity dependencies before the final file.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local translation and polarity dependencies. The printed rule-preservation
theorems reported no `sorryAx` dependencies.
