# Lean source status

The files in this directory target the ProveIt `ConciseIPRA` API at the audited repository snapshot and the pinned Lean 4.32.0 toolchain.

They are organized as follows:

- `CIFER/ObjectCompiler.lean`: object-language residual composition, loop composition, stable observations, and native export.
- `CIFER/ResidualGraph.lean`: executable host graph and residual extraction definitions.
- `CIFER/DemandClosure.lean`: finite demand vectors and inflationary iteration definitions.
- `CIFER/Relational.lean`: finite witness clouds, viability-step definitions, and stability interfaces.
- `CIFER/ApplicationTargets.lean`: honest conditional interfaces for height/list, descent covers, gaps, and analytic estimates.
- `FORMALIZATION_PLAN.md`: exact dependency-ordered path to a completed embedded development.

No Lean executable was available in the artifact runtime, so no elaboration claim is made. The source intentionally contains no `sorry` and declares no axiom. Theorems not yet proved are recorded as comments and milestones rather than admissions.
