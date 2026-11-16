# Forward PAeq symmetry axiom

This package proves the actual forward translation of the fixed PAeq symmetry sentence and connects it to the root formula dispatcher. Its source proof reverses the two isomorphism witnesses for translated equality, using the independently replayed full-source inverse-isomorphism proof and its closed Separation axiom. `PA194ForwardSymmetry.root_symmetry_provable` proves, in each candidate PRA model satisfying IΣ₁ and under the root packet code bound, that the full relational source theory proves the dispatcher's exact translation of `symmetry.univCl`.

This is a model-level fixed-axiom supplier, including nonstandard arithmetic models. It does not construct a complete source-proof compiler, prove the arbitrary induction-axiom supplier, establish physical-machine synchronization, or prove an iPRA consistency implication.

Reproduce from the repository root with a new empty output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-forward-symmetry.sh "$PWD" /dev/shm/pa194-forward-symmetry-repo-NEW
```

The checker rebuilds nine source modules and an eleven-report audit using the separately replayed full-source inverse-isomorphism result and other explicitly listed retained prebuilt overlays. It does not rebuild the full import closure.

The [normalized identity-packet bridge](IDENTITY-FIXED.md) now supplies this closed fixed axiom for the guarded route. Specializing the guarded endpoint to normalized packets remains a separate step.
