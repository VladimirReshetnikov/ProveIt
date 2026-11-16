# Forward PAeq transitivity axiom

This package proves the actual forward translation of the fixed PAeq transitivity sentence and connects it to the root formula dispatcher. Its source proof uses the independently replayed transitivity of translated equality and discharges the composition-specific Separation instance in the full relational source theory. The explicit typed equality template and its substitution lemma keep three-quantifier syntax normalization tractable.

`PA194ForwardTransitivity.root_transitivity_provable` proves, in each candidate PRA model satisfying IΣ₁ and under the root packet code bound, that the full relational source theory proves the dispatcher's exact translation of `transitivity.univCl`. This is a model-level fixed-axiom supplier, including nonstandard arithmetic models. It does not construct a full guarded proof compiler, supply arbitrary induction axioms, establish physical-machine synchronization, or prove an iPRA consistency implication.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-forward-transitivity.sh "$PWD" /dev/shm/pa194-forward-transitivity-repo-NEW
```

The checker rebuilds six source modules and a seven-report audit. It gives precedence to the repository-replayed equality-transitivity, composition-source and composition-transitivity objects at `/dev/shm/pa194-equal-transitivity-repo`, `/dev/shm/pa194-composition-source-repo`, and `/dev/shm/pa194-composition-transitivity-repo`; remaining imports are the explicitly listed prebuilt paths. It does not rebuild the full dependency closure.
