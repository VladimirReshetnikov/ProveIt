# Lean formalization outline

Target environment: the ProveIt root workspace at Lean **4.32.0**.

Suggested placement:

```text
Logic/PrimitiveRecursiveArithmetic/FRNF/Lean/FRNF.lean
Logic/PrimitiveRecursiveArithmetic/FRNF/Lean/FRNF/*.lean
```

and add a `lean_lib` entry with `srcDir` pointing to that `Lean` directory.

## Status

- `FRNF/Kernel.lean` contains no `axiom` or `sorry`; it is a repository-aligned
  source candidate for the generic logical layer.
- `FRNF/Semantic.lean` is a small host-level semantic model.
- `FRNF/ObjectTargets.lean` is deliberately a blueprint.  Its visible
  placeholders are the remaining object-arithmetic work.
- Lean was unavailable in the artifact environment, so none of these files is
  claimed to have passed `lake build`.

## Completion order

1. Build `Kernel.lean` in the root workspace and adjust only API drift.
2. Define encoded finite tables using the checked pairing and simultaneous
   recursion modules.
3. Implement bounded-formula Booleanization and inspect axioms.
4. Reify the dual-horizon reverse pass and its QF invariant.
5. Implement backward viability using `Core.Search.search_found`.
6. Add metric error-budget arithmetic, guarded reciprocal, and finite-net
   modules.
7. Run `#print axioms` on every exported theorem and transfer final results
   through `pra_iff_native`.
