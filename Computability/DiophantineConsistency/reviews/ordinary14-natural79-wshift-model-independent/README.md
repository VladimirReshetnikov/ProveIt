# Independent source review: natural-79 to natural-80 w shift

The [source proposal](../../research/ordinary14-natural79-wshift-model-draft/README.md) states the correct changed-valuation identity and conditional zero-existence transfer between the pinned literal 79- and 80-operation graphs. No Lean theorem, axiom report, iPRA result, provider closure or physical-file/PDF binding is established by this review.

The receipt compares every JSON row: the 80 graph's only removed node is `w=n_w+1`, and each use of that node is changed to `n_w` in the 79 graph. The two whole Lean graph sources likewise differ only by that deletion, its consumer substitution, and the namespace rename. Thus, over a commutative ring, the 79 output at `v` equals the 80 output at `v` with slot 6 replaced by `v 6-1`, by exact structural congruence. It is not a same-valuation assertion. Literal source correspondence and its interpretation in Lean remain subject to separate elaboration.

The proposed natural-model relation sets `v79 6=v80 6+1` and preserves every other coordinate. Its 79-to-80 existential map assumes every 79 zero has `v 6>0`, obtains a predecessor, explicitly uses `add_comm` for the witness equation, and applies the proposed related-valuation equivalence in the forward direction. The reverse map increments coordinate 6 and uses the reverse direction. The source does not prove the positive-w premise. Supplying it requires the separate model factor and divisibility work; the external standard-integer argument does not automatically prove the model statement.

Both the original checker and this bounded independent source receipt reproduce. The proposed tactic proofs, natural predecessor/coercion handling, model interfaces, selected port assumptions and three `#print axioms` commands remain unelaborated and unexecuted.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-wshift-model-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-wshift-model-independent/result.json
```
