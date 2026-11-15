# Environment independence for internally closed PAeq formulas

For every internally valid PAeq term code `t`, including nonstandard codes, `closedTermEnvironment` proves that `termFreeBound t = 0` makes its translation independent of the packet's free environment whenever its bound vector and result term agree. `closedAtomEnvironment` applies this to both terms of an equality atom.

For every internally valid PAeq formula code `p`, `closedFormulaEnvironment` proves that `formulaFreeBound p = 0` makes its translation independent of both the free environment and the result field, whenever the packets' bound vectors agree. Neither theorem assumes a length bound or packet validity. Both structural-induction predicates are explicitly shown Π₁, and the proofs apply in every model of IΣ₁, including nonstandard models.

`closedTranslate_packets` specializes this to any two valid packets with source arity zero, whose bound vectors are both empty. `closedInduction_freeBound` proves that the existing modeled closure operation gives an actual zero free-variable bound. Consequently, for every internally valid arity-one induction property, `closedInduction_root_packet` identifies the root-packet translation of its fully closed induction axiom with its translation under every valid source-arity-zero packet, including an identity packet. This is an exact formula-code equality, not yet a source-theory proof of the translated induction axiom or a guarded proof compiler.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-closed-environment.sh "$PWD" /dev/shm/pa194-closed-environment-repo-NEW
```

The checker rebuilds four source modules and a seven-report axiom audit. It uses the existing retained PAeq closure, arithmetic syntax, dispatcher, Foundation, and package objects from the paths explicitly enumerated in the checker; it does not rebuild the full dependency closure.
