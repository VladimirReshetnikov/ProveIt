# An internal PA singleton witness

`PA194InternalSingleton.internal_PA_singleton_explicit` proves that, for
every model-valued `a`, Foundation's internal PA proves the explicit
arithmetic formula

`∃s ∀x (bit(x,s) ↔ x=a)`.

The model is any `ORingStructure` whose arithmetic reduct satisfies IΣ₁;
`a` may be nonstandard. The theorem is about a syntactic internal PA proof,
not an assertion that an external satisfaction predicate can evaluate an
arbitrary nonstandard formula.

The construction proves the fixed standard singleton sentence in IΣ₁ by
ordinary first-order completeness and the model's singleton bit-set law,
then quotes that fixed proof into the model. It specializes the internal
universal proof at the model-valued free label `a` and checks that the
resulting coded formula is exactly the displayed typed formula.

This supplies a potential witness ingredient for the guarded gate, especially
its equal-label case. It does not prove bounded comprehension for arbitrary
internal formulas, the negated separation-tail premise, guarded-gate
preservation, an iPRA implication, or a finite proof transformer.

`check-internal-singleton.sh` is a full dependency rebuild and requires the
matching audited `IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY`. Because of
disk I/O pressure, the present check was a focused single-module rebuild
against retained prerequisite objects; it passed with no `sorryAx`. The full
nested rebuild is deferred.

An independent suffix replay rebuilt the singleton module against separately
checked diagonal and earlier source objects, with retained deeper prerequisite
overlays. It passed without `sorryAx`; this was not a full prerequisite replay.
