# Uniform internal ordinal-induction proof-code constructor

For every PRA model with IΣ₁ arithmetic reduct and any internal theory, every internally valid arity-one source property code p, including nonstandard p, is mapped to an actual internal proof of `ordinalInductionCode p`, given a singleton proof of the separation root for the negated property and eight specified fixed universal source-theorem proofs. `uniformOrdinalProof` constructs the typed proof; `uniformOrdinalProof_val` identifies its exact value as `uniformOrdinalCode`; `uniformOrdinalCodeGraph_defined` proves that a single fixed Σ₁ graph defines the code on all model inputs. The constructor explicitly introduces the two implication disjunctions and does not choose a proof at the packaging step.

The separation and eight fixed universal proofs remain explicit inputs, and the theorem is model-level. It does not by itself supply a uniform separation proof code, prove a native iPRA theorem, establish the complete PA interpretation or machine simulation, or prove the PA194 equivalence. The checker recompiles the new source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-uniform-ordinal-proof.sh "$PWD" /dev/shm/pa194-uniform-ordinal-proof-repo
```

Choose a fresh output for another run.
