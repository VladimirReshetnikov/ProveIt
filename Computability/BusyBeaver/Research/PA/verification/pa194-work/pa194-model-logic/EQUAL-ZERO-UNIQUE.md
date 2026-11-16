# Source-theory uniqueness matrix for zero

`PA194EqualZero.unique` is a Foundation natural-deduction proof: from the exact typed translated formulas for `x = 0` and `y = 0`, it derives the exact typed translation of `x = y`, given source equality principles. The proof opens both pairs of translated equality witnesses; `zeroFromIsoReverse` shows that each compared representative is zero from its isomorphism to a zero witness, and `emptyOrderIso` constructs an isomorphism between them. It does not use extensionality, inverse/composition graphs, or any PA arithmetic axioms.

`PA194EqualZeroElimination` defines the concrete translated equality-to-zero formula, its shift law, and a proof-preserving elimination with the two fresh witnesses. `PA194OrderIsoZeroReverse` is a source-logic proof that the source of an isomorphism to a zero object is zero. The final module uses the separately source-replayed `/dev/shm/pa194-empty-order-iso-replay` (a repository-built copy is available at `/dev/shm/pa194-empty-order-iso-repo`).

From the repository root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-equal-zero-unique.sh "$PWD" /dev/shm/pa194-equal-zero-unique-repo-NEW
```

The checker source-builds three modules and a seven-report audit in a single output, rejecting `sorryAx`. It retains the separately replayed empty-isomorphism object and prebuilt dependencies listed in the checker, including Foundation. It is a typed source-logic matrix; the quantifier wrapper, exact numeric translation, guarded field, and native iPRA result require additional theorems.
