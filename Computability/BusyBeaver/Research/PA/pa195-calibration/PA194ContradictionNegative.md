# Negative translation at source code 1

`PA194ContradictionNegative.lean` complements the positive-code result in
[the contradiction translation](PA194ContradictionTranslation.md). In every
nonempty candidate-PRA model whose arithmetic reduct satisfies IΣ₁ and whose
equality is interpreted as equality, the negative output of the fixed source
translator at code `1` is exactly the Foundation quote of
`∼PA194ContradictionTranslation.contradiction`. The proof combines the
all-model syntactic-polarity theorem with the positive output identification.
It has no decoder-certificate premises, and Lean reports only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

The identified object is one fixed standard formula, not a proof-code
translation or a machine/consistency implication. The object-theory IΣ₁ and
PA proofs of its universal closure are recorded in the linked package.
Run `check-contradiction-negative.sh` with the audited overlays set.

The full author replay passed with the audited overlays and no `sorryAx` in
the reported theorem dependencies.
