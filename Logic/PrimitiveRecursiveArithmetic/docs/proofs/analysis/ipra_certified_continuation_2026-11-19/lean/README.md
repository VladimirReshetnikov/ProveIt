# Lean reference layer: uncompiled

This directory is a formalization blueprint, not a completed iPRA development.

| Module | Contents | Status |
|---|---|---|
| `FeedbackReference.lean` | Full candidate proofs of finite rational row domination, contraction, increments, tails, and residual comparison | Uncompiled ambient Lean candidate |
| `PolynomialBlueprint.lean` | Polynomial code operations, normalization, shift, preconditioned update, gain checker, orbit, residual, precision clock, goals | Definitions and unproved Prop obligations |
| `FactorBlueprint.lean` | Coefficient convolution, Sylvester map, inverse checker, norm, actual lifting recurrence, residual, clock, goals | Definitions and unproved Prop obligations |
| `ClusterBlueprint.lean` | Numeric graph/mask/permutation programs, bounded selector, covers, locators, goals | Definitions and unproved Prop obligations |
| `OdeBlueprint.lean` | Rational norms, coefficient contracts, Euler nodes/polygons/residuals, outputs, quadrature, goals | Definitions and 16 unproved Prop obligations |

No new axioms or `sorry` proofs are used to turn the blueprint goals into
asserted theorems. This syntactic property is not evidence of successful
elaboration. In particular, a structure listing proof obligations has no
supplied inhabitant.

The numerical reference programs may use ordinary Lean types and quantification
over functions. Before claiming primitive-recursive uniformity, instantiate
those functions with one fixed PR template or the explicit polynomial/companion
interpreter. The report's internal endpoints quantify over numbers and require
actual `Prf PRAAx` values.

For proof order, exact numerical invariant statements, and existing ProveIt
dependencies, read the report's Lean section and `FeedbackObjectPort.md`.

The intended initial commands are:

```bash
lake update
lake build
lake env lean AxiomAudit.lean
```

Lean was unavailable in the delivery environment, so these remain instructions
for subsequent checking. The version pin is the inspected ProveIt baseline:
Lean 4.32.0, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
