# Forward PAeq symmetry axiom

This package proves the actual forward translation of the fixed PAeq symmetry sentence and connects it to the root formula dispatcher. Its source proof reverses the two isomorphism witnesses for translated equality, using the independently replayed full-source inverse-isomorphism proof and its closed Separation axiom. `PA194ForwardSymmetry.root_symmetry_provable` proves, in each candidate PRA model satisfying IΣ₁ and under the root packet code bound, that the full relational source theory proves the dispatcher's exact translation of `symmetry.univCl`.

This is a model-level fixed-axiom supplier, including nonstandard arithmetic models. It does not construct a complete source-proof compiler, prove the arbitrary induction-axiom supplier, establish physical-machine synchronization, or prove an iPRA consistency implication.

Reproduce from the repository root with a new empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-forward-symmetry.sh "$PWD" /dev/shm/pa194-forward-symmetry-repo-NEW
```

The checker rebuilds nine source modules and an eleven-report audit using the separately replayed full-source inverse-isomorphism result and other explicitly listed retained prebuilt overlays. It does not rebuild the full import closure.

The [guarded compiler](../pa194-guarded-compiler/README.md) uses identity packets rather than `rootParameters`; the correspondence of this closed axiom translation across those packets remains to be proved.
