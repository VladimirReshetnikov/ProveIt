# Lean blueprint

These files target the ProveIt `ConciseIPRA` object-language API at repository snapshot `34816faca8aa605999290b41d26210753b5c3b38`.

## Status

- `PFIG/ExactCore.lean` contains source-complete contract and observer combinators adapted from inspected repository files. It has no `sorry`, but was not compiled in this artifact environment.
- Every file whose name contains `Blueprint` is intentionally incomplete and contains explicit `sorry` targets or schematic structures.
- No theorem in this directory is claimed to have been kernel-checked as part of this delivery.

## Integration

Place `PFIG/` under a Lean source root that can import `ConciseIPRA.PR`. The first integration step should replace the migration targets in `ObjectLoopBlueprint.lean` by importing the repository's source-complete `primitiveRecursionInvariant` and `primitiveRecursionAt` proofs.

Suggested audit commands after integration:

```lean
#print axioms LeanProofs.ConciseIPRA.PFIG.ExactContract.compose
#print axioms LeanProofs.ConciseIPRA.PFIG.ObjectLoop.LoopContract.sound
#print axioms LeanProofs.ConciseIPRA.PFIG.NegativeTransfer.retained_transfer_target
```

Search the final source tree for `sorry`, `axiom`, and target-only `def ... : Prop` declarations before marking any module object-complete.
