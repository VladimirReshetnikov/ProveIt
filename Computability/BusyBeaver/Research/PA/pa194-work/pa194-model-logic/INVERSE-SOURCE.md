# Full-source order-isomorphism symmetry

The source isomorphism reversal proof in the separately replayed inverse construction assumes a graph-parameter-closed Separation instance. This package constructs a fixed two-parameter property, proves its Separation instance has free-variable supremum 2, and identifies its exact universal closure with `closedInverseSeparation`. It proves that this fixed sentence is an actual axiom of `adjunctiveFullSepTheory`, then specializes it at each standard source-variable index and discharges all the other source axioms.

`PA194InverseSymmetrySource.inverseSymmetrySourceProof a b` is a source proof of `(domain a ∧ orderIso a b) → orderIso b a` for each standard Lean index pair `a b`, in every candidate PRA model satisfying IΣ₁, including nonstandard arithmetic models. It is a model-level open-formula proof, not a uniform internal-index proof-code graph, an actual translated PAeq axiom, or a native iPRA implication.

Reproduce from the repository root with a new empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-inverse-source.sh "$PWD" /dev/shm/pa194-inverse-source-repo-NEW
```

The checker rebuilds five source modules and a six-report audit. It relies on the separately replayed inverse source construction `/dev/shm/pa194-inverse-symmetry-repo` and the other prebuilt paths listed in the checker; the complete import closure is not rebuilt.
