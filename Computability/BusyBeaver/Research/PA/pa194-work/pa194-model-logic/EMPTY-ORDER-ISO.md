# Isomorphism between empty representatives

`M6.PA.RelationalSource.PairGraph.emptyOrderIso` constructs, in Foundation natural deduction, an actual order-isomorphism between any two zero representatives from the source equality principles and proofs that the representatives are zero. It does not identify the representatives or assume source extensionality. The proof chooses the first representative as an empty graph: `emptyGraphTyped` and `emptyGraphRightTotal` handle the two clauses that change from the already-established identity bijection; `emptyGraphEntries` handles graph entries.

From the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-empty-order-iso.sh "$PWD" /dev/shm/pa194-empty-order-iso-repo-NEW-new
```

The checker recompiles the module and rejects `sorryAx`, requiring three clean axiom reports. The source-theory premises remain explicit and the checker retains the prebuilt dependencies listed in its `LEAN_PATH`, including Foundation. This typed source natural-deduction lemma does not by itself prove the guarded zero-uniqueness field, an arithmetic model theorem, or native iPRA equivalence.
