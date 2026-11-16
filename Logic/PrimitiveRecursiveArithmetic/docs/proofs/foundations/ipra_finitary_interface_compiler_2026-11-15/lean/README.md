# Lean outline

These modules target the checked `ConciseIPRA` API at ProveIt commit
`9df5cbdf39e6220be823f611987bd584d37711fd`.

They are **not kernel-checked in this archive**. Lean was unavailable in the
artifact runtime, and visible `sorry` terms intentionally mark every unfinished
obligation. The strongest source-level component is
`ObjectTraceCompiler.lean`: it gives the exact formulas, de Bruijn layouts,
primitive-recursion equations, and four small proof milestones for the generic
`Prf PRAAx` trace-reflection theorem.

Suggested order:

1. `ObjectTraceCompiler.lean`
2. `BoundedFormulaCompiler.lean`
3. `RelationalWitnesses.lean`
4. `CertifiedProgram.lean`
5. `ApplicationTargets.lean`

See `LEAN_PLAN.md` and `FORMALIZATION_STATUS.md` for the completion path and
status conventions. A future CI gate should reject `sorry`, `admit`, explicit
new axioms, and unintended imports before any theorem is called formalized.
