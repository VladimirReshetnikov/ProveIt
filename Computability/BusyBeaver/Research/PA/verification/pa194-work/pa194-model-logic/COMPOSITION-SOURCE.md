# Full-source order-isomorphism transitivity

The separately replayed composition construction assumes a graph-parameter-closed Separation instance. This package constructs the corresponding fixed three-parameter property, proves the Separation instance has free-variable supremum 3, and identifies its exact universal closure with `closedCompositionSeparation`. It proves that the closed sentence is an axiom of `adjunctiveFullSepTheory`, specializes it at each standard source-variable index, and discharges the other source axioms.

`PA194CompositionSymmetrySource.compositionSourceProof a b c` is a source proof of `(domain a ∧ orderIso a b ∧ orderIso b c) → orderIso a c` for each standard triple of indices, in every candidate PRA model satisfying IΣ₁, including nonstandard arithmetic models. It is a model-level open-formula proof, not a uniform internal-index proof-code graph, an actual translated PAeq axiom, or a native iPRA implication.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-composition-source.sh "$PWD" /dev/shm/pa194-composition-source-repo-NEW
```

The checker rebuilds five source modules and a six-report audit using the separately replayed 29-module composition construction and other explicitly listed prebuilt paths. It does not rebuild the full dependency closure.
