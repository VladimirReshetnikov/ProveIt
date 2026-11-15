# Internal ordinal induction provable in every relevant model

For every PRA model whose arithmetic reduct satisfies IΣ₁, and every model-valued code p satisfying the internal arity-one source-syntax predicate, `ordinalInductionInternalProvable` establishes in Lean that the full adjunctive-plus-separation source theory internally proves `ordinalInductionCode p`. This includes nonstandard p. It derives the universally quantified domain conclusion from contextual base and step via the bad-domain-point contradiction, then discharges base and step through the already checked sequent-packaging theorem. `ordinalConclusionFromBaseStep` gives the intermediate contextual internal derivation. There is no induction-sequent or separation assumption on this theorem beyond the stated model and syntax hypotheses.

This is a metatheorem about all such Lean models, using model-level choice in source proof selection and packaging. It does not yet provide a single fixed Σ₁ graph for its overall proof code, is not itself a native iPRA derivation, and does not prove the PA194 machine equivalence. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-internal-ordinal-from-bad.sh "$PWD" /dev/shm/pa194-internal-ordinal-from-bad-repo
```

Choose a fresh output for another run.
