# Lean status

- Runtime had no `lean` and no `lake`; no compilation was possible.
- `NativeClauseFramework/Bridge.lean`: candidate direct integration code, no
  `sorry`, not checked here.
- `ProgramBlueprint.lean`, `TraceBlueprint.lean`, `DemandBlueprint.lean`,
  `RelationalBlueprint.lean`, and `ApplicationsBlueprint.lean`: outlines with
  explicit proof holes.
- No file in this package is claimed kernel-checked.
- Upstream declarations reused by the design are kernel-checked in the pinned
  ProveIt repository according to that repository's status documentation.
