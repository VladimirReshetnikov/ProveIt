# Lean implementation skeleton

These files are aligned with the public APIs visible at ProveIt commit
`7fa3ba48e8f62e8018ed954faaa48b908217eaf1`.

They are **not claimed to have been compiled** in this archive: Lean was not
installed in the artifact runtime. `PCFM/Core.lean` and the low-level
`InvariantSpec` in `PCFM/Trace.lean` are intended to be close to directly
buildable. The remaining files separate implemented data definitions from
commented target theorems; they do not introduce `sorry`, `admit`, or axioms.

Suggested repository placement:

```
Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/
  IPRADerivations/Framework/...
```

The first repository-side validation command is:

```
lake build IPRADerivations
```

After exact notation/import adjustments, implement in this order:

1. Boolean truth tables.
2. `reflectQF`.
3. bounded universal/existential wrappers.
4. higher-level trace construction.
5. exact stable observer.
6. backward viability.
7. open bridge normalization and wrappers.
