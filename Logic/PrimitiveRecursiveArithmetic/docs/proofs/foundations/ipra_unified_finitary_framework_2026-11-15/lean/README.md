# Lean blueprints

These files give a source-oriented completion path against ProveIt's checked
`ConciseIPRA` API at commit
`b88e843c31b50dfe461bfbd0380166ca422cd3ab`.

## Exact status

- `TraceCompilerBlueprint.lean` identifies the intended object-language
  formulas, local proof record, and theorem returning a `Prf PRAAx` derivation.
  Its central definitions and theorem contain `sorry`.
- `RelationalRefinementBlueprint.lean` gives the finite semantic definitions
  of viability/full viability and states the shrinking theorem.  Its universal
  theorems contain `sorry`; it has not been compiler-checked.
- `ApplicationTargets.lean` records the next guarded-real, finite-net, and
  height/list endpoints.  The `True` declarations are target notes, not proofs
  of the mathematical applications.

No Lean executable was available in the artifact environment.  These files are
not represented as kernel-checked.  The report's Section 13 and `ROADMAP.md`
give the dependency order needed to replace every placeholder.
