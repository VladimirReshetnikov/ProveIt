# A direct separation trace is a subset of its source

In every PRA model with IΣ₁ arithmetic reduct and any internal theory, from a supplied direct separation-trace derivation construct a derivation that the witness is a subset of the source. The property and source/witness indices may be arbitrary model values, including nonstandard ones. The construction shifts the trace, proves the membership implication at a fresh variable, and universally quantifies it. The exact proof code and a fixed Σ₁ graph defining it are checked; logical disjunction introduction uses the explicit proof-code constructor.

The trace derivation remains a premise; this does not itself give nonemptiness, least witness elimination, ordinal induction, or an iPRA machine theorem. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-trace-subset.sh "$PWD" /dev/shm/pa194-trace-subset-repo
```

Choose a fresh output for another run.
