# Closed internal ordinal induction for all internal properties

For every PRA model whose arithmetic reduct satisfies IΣ₁, and every internally valid arity-one property code p, including nonstandard codes, the universally closed ordinal-induction code `closedOrdinalInductionCode p` is internally provable in the full adjunctive-plus-separation source. The proof applies the previously established open internal induction metatheorem and the existing arbitrary model-length closure theorem.

This is a Lean metatheorem about such models and retains the model-level choice of the underlying proof. It does not by itself construct a fixed Σ₁ code graph for the model-length closure operation, complete the arithmetic interpretation or establish a native iPRA machine equivalence. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-closed-internal-ordinal.sh "$PWD" /dev/shm/pa194-closed-internal-ordinal-repo
```

Choose a fresh output for another run.
