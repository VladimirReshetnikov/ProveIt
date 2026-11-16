# Forward PAeq multiplication-zero axiom

This package constructs a natural-deduction source proof of the exact forward translation of the fixed PAeq axiom `mulZero` and lifts it to the actual root formula dispatcher. In `PA194ForwardMulZero.root_mulZero_provable`, in every candidate PRA model satisfying the induced IΣ₁ assumptions and for every modeled root parameter `d`, the source theory proves the exact translation of `mulZero.univCl`, provided its code is below the root packet length. This is a modeled source-provability result, including nonstandard models. It is not a native iPRA theorem, a PA-refutation compiler, or a physical-machine synchronization theorem.

The source derivation constructs the multiplication trace using a one-point graph: a zero vertex has no predecessor, so the recurrence holds vacuously, and the required output is zero. Its explicit proof assumptions are formula equality, empty set, adjunction, and the reflexivity of the source ordinal order-isomorphism; the context and source modules discharge those assumptions through the existing source-theory suppliers.

Reproduce from the repository root, with a new empty output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-forward-mul-zero.sh "$PWD" /dev/shm/pa194-forward-mul-zero-repo-NEW
```

The checker rebuilds `PA194FoundationAdditionZero` and `PA194FoundationAdditionZeroExistence` from their repository source files, then builds all 14 package source files in the output and checks fifteen named axiom reports for `sorryAx`. Other imports, including `PA194FoundationAdditionTrace`, generic rewriting and ordinary syntax, source suppliers, the Foundation libraries and package dependencies, are retained prebuilt objects from the explicitly enumerated `LEAN_PATH` overlays in the checker. They are not rebuilt or independently audited by this run. Full source-closure replay is therefore not claimed.
