# Reducing `nameOfEq` to two naming fields

`PA194GuardedCompiler.nameOfEq` proves the exact `NameFacts.nameOfEq` field conditionally for any Δ₁ source theory, every internally valid arity-zero PAeq term and every model-valued free-variable index, including nonstandard codes. Its explicit `NameOfEqPrereqs` structure assumes precisely the `uVar` and `atomTransfer` fields. The generic logical `nRefl` and `nameOfUniq` results are used as proved dependencies, not assumptions. In particular, this module does not establish `atomTransfer`.

The open-sequent proof first uses `uVar` and `nameOfUniq` to derive that `j=c` supplies `nameAll c j`; `atomTransfer` then transfers `c=t` to `j=t`, with `nRefl t` supplying the unchanged second term. The final module introduces the guarded universal while shifting its context, without requiring an arbitrary term witness.

From the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-name-of-eq.sh "$PWD" /dev/shm/pa194-name-of-eq-repo-NEW-new
```

The checker recompiles both modules with one clean axiom report each and rejects `sorryAx`, retaining the repository-built `nameOfUniq`, `nRefl`, open consequence, substitution and universal-left overlays, and other prebuilt objects listed in the script including Foundation. It is a model-uniform Lean reduction over IΣ₁ arithmetic structures; it is not a native iPRA theorem or a complete interpretation.
