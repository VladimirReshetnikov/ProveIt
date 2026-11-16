# Universal-opening shape over internal lengths

The `PA194QVecHistory` module constructs an internal sequence iterating Foundation's `qVec` operation over an arbitrary model length. `PA194QVecDistribution.distribution` uses such a sequence and IΣ₁ induction to distribute an arbitrary internal substitution through an arbitrary model-length `qqAlls` block. Its corollary `free_all_iter_exists` shows that Foundation `free` preserves the length of a block of universal quantifiers.

`PA194OpeningShape.history_shape` applies this fact to the decoder-and-opening history starting at `qqAlls p n`, where `p` is internally well formed at depth `n`. It certifies that every entry before the n-th opening is a universal formula with a well-formed body. `open_block_provable` then combines the certificate with the earlier soundness theorem: if internal PA proves that universal block, there is a constructed n-step opening history whose every entry is internally PA-provable. These conclusions hold in arbitrary IΣ₁ arithmetic models, including nonstandard p and n.

The theorem does **not** yet identify the final entry with `subst (fvarVec n) p`. It also does not construct the Foundation induction-axiom recognizer's closure witnesses, establish arbitrary-formula PA induction or bounded comprehension, discharge the distinct-label gate, or prove an iPRA implication.

The author replay ran `check-opening-shape.sh`, rebuilding the five local modules against the pinned Foundation overlay. The printed axioms contain only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
