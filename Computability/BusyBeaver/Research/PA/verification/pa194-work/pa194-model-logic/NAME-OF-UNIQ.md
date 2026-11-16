# Logical `nameOfUniq` field

`PA194GuardedCompiler.nameOfUniq` proves the exact `NameFacts.nameOfUniq` field for any Δ₁ source theory, every internally valid arity-zero PAeq term `t`, and every model-valued free-variable index `c`, including nonstandard codes. It assumes no source axioms, semantic term properties, other naming fields, or arithmetic induction supplier. It introduces the guarded universal in the target naming formula and applies the separately replayed open uniqueness consequence in the shifted context. The accompanying `shift_uniq` is the exact source-code shift law for arbitrary internal terms; `free_orA` and `free_negA` handle the opening of the formula.

From the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-name-of-uniq.sh "$PWD" /dev/shm/pa194-name-of-uniq-repo-NEW-new
```

The checker rebuilds both modules, requires four clean axiom reports and rejects `sorryAx`. It retains the separately source-replayed open consequence and the repository-built uniqueness-substitution and universal-left overlays, plus prebuilt dependencies listed in the script including Foundation. The result is model-uniform over IΣ₁ arithmetic structures; it is not an object-level iPRA theorem, an entire `NameFacts` instance, or the machine equivalence.
