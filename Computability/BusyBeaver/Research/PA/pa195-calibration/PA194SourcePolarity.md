# Syntactic polarity of the named-source translation

`PA194CloseNegation.lean` proves that the Foundation internal formula-closing
traversal commutes with Foundation's internal syntactic negation. The input
formula, its well-formedness depth, and the selected label may be nonstandard
model elements. The proof is Σ₁ structural induction on internal formulas,
using the earlier term-vector and formula well-formedness results.

`PA194SourcePolarity.lean` uses that commutation and the all-model output
well-formedness proof to show that, for every internal PA194 named numerical
source code, the negative component of the explicit dual translation is
**exactly the internal syntactic negation** of its positive component.
`all_pol` retains explicit candidate-PRA certificates for the source-tag and
both child decoders. `fixed_all_pol` uses the previously fixed certified
decoders and has no certificate premises. Both assume a nonempty
candidate-PRA model, equality interpreted as equality, and an IΣ₁ arithmetic
reduct; the source code may be nonstandard. Lean prints the fixed theorem's
signature and reports only `propext`, `Classical.choice`, and `Quot.sound` for
the printed results, with no `sorryAx`.

This is a relation between **internal syntax codes**. It does not establish a
semantic truth predicate for nonstandard formulas, a translation of PA proofs
or refutations, correctness of the complete compiler, or either PA194
machine/consistency implication. The named numerical source syntax and
Foundation's relational-source syntax have distinct encodings and require a
separate syntax/proof bridge.

Run `check-source-polarity.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set. It rebuilds the formula closer, source
translation and well-formedness dependencies before checking both modules.

The full author replay passed with the audited overlays and no `sorryAx` in
the checked dependencies. An independent full replay is also in progress.
