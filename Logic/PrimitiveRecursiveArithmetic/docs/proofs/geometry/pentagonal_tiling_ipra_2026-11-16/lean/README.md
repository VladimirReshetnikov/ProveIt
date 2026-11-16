# Lean contents

`PentagonalTilingBlueprint.lean` is a compile-oriented interface and arithmetic
sanity layer.  It contains no `sorry`, `admit`, or added axiom, but it was not
compiled in this delivery environment because Lean/Lake are not installed
there.

The intended repository workspace is:

```text
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean
Logic/PrimitiveRecursiveArithmetic/Derivations/Lean
```

The endpoint is not a Mathlib theorem about real-plane sets.  It is an explicit
closed derivation

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] verifyType15Fm
```

for a fixed primitive-recursive certificate checker, followed by the generic
certificate-soundness development described in `../FORMALIZATION_PLAN.md`.
