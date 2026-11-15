# Transitivity of the translated equality relation

`equalEliminate` exposes the two value witnesses and the connecting order isomorphism of the actual forward-translated equality formula, preserving a shifted context. `alignMiddle` uses primitive source equality to identify the two interpretations of the shared middle variable. `equalTransitivity` then composes the isomorphisms and constructs the target translated equality.

This is a source natural-deduction proof under explicit `Inputs`: source equality, empty set, adjunction, intersection, and the particular universally closed Separation instance for composition. That Separation instance is independently supplied in the full-source composition proof. This package does not prove the universally quantified PAeq transitivity axiom, an internal proof-code graph, or a guarded compiler.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-equal-transitivity.sh "$PWD" /dev/shm/pa194-equal-transitivity-repo-NEW
```

The checker rebuilds six source modules and a six-report audit. It uses the separately replayed full-source composition and translated-equality dependencies and other explicitly listed prebuilt paths; it does not rebuild the full dependency closure.
