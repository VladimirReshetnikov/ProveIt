# TAPIR Lean sources

These files target the pinned ProveIt commit
`58627ed89814ba122e1f0f012f1aba103cda267b`.

## Status

- `Kernel.lean`: no intentional placeholders; unelaborated source candidate.
- `Schedule.lean`: no intentional placeholders; unelaborated source candidate.
- `Certificates.lean`, `SearchK.lean`, `Reflection.lean`, `Trace.lean`, and
  `Examples.lean`: explicit blueprints with `sorry` milestones.

No Lean or Lake executable was installed in the artifact build runtime.  The
archive therefore claims no new kernel-checked declaration.

## Suggested destination

Copy this directory to:

`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/TAPIR/`

Then change the imports from `TAPIR.Kernel` to the full project module path as
needed and follow `../FORMALIZATION_PLAN.md`.
