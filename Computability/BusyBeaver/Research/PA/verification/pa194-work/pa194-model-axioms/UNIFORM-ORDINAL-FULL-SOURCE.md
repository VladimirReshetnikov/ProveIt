# Supply the explicit ordinal proof constructor in the full source

For every PRA model whose arithmetic reduct satisfies IΣ₁ and every internally valid property code, including nonstandard codes, the full adjunctive-plus-separation source supplies all nine seed proofs needed by the fixed-Σ₁-graph uniform ordinal proof constructor. The wrapper produces an actual internal proof of `ordinalInductionCode p` using that constructor. The source selects the property-dependent separation proof and fixed universal proofs at model level using choice.

This does not prove the selected seed proofs form a uniform definable function of p, construct a uniform proof of the universally closed induction code, identify the translation of ordinary PA induction, or establish a native iPRA machine equivalence. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-uniform-ordinal-full-source.sh "$PWD" /dev/shm/pa194-uniform-ordinal-full-source-repo
```

Choose a fresh output for another run.
