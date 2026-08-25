# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — exact forward and inverse curvature profile
branch/base: codex/fabius-both-papers synchronized with origin/main at
  6fcbbb5da45330bdc78c6090706cf1479f3d3afb
writing: Lean/FabiusFunction/Convexity.lean,
  Lean/FabiusFunction/FabiusInverse.lean, README.md,
  docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.{tex,pdf},
  docs/fabius_lean_walkthrough/fabius_lean_walkthrough.{tex,pdf},
  docs/non-formalized-research-frontiers/non-formalized-research-frontiers.{tex,pdf},
  this registry
reading: Differential.lean, Monotonicity.lean, current inverse calculus and
  exact smoothness/steepness APIs, inverse research-frontier status ledger
expected API: exact second-derivative formula, global sign and zero loci for
  `fabiusReal`; midpoint first/second inverse derivatives; exact interior sign
  and zero loci for the inverse curvature; divergence of the interior inverse
  derivative at both clamping endpoints
completed: integrated the exact global forward second-derivative formula and
  sign/zero loci in Convexity; integrated the inverse midpoint jet, interior
  sign/zero loci, and both endpoint derivative limits in FabiusInverse; updated
  the README focused API and shape summary; committed the Lean/API tranche as
  `eaea1b9afe2b7ff0b7dd880bd1710e303dec6d80`; updated the primary exposition,
  published walkthrough, and consolidated research-frontier status ledger;
  repinned the walkthrough and integration-frontier source claims to that code
  commit and rebuilt all three paired PDFs in three passes
validated: direct Lean elaboration and focused Lake builds pass for both
  `FabiusFunction.Convexity` (2661 jobs) and
  `FabiusFunction.FabiusInverse` (3248 jobs); the facade-only
  `/tmp/FabiusCurvatureFacadeAudit.lean` resolves every new declaration,
  passes `assert_no_sorry`, and reports exactly `[propext, Classical.choice,
  Quot.sound]`; all three final LaTeX logs were free of undefined/multiply
  defined references and errors, and rendered-text checks find the new names,
  exact pin, and no `??`; `git diff --check` is clean
next: run independent final documentation/source-coherence review, commit the
  TeX/PDF/registry batch, merge the latest origin/main, and rerun
  focused/facade checks before pushing main and the feature branch
lease: acquired 2026-08-25T15:04:47-07:00; expires 2026-08-25T16:04:47-07:00
git owner / build owner: /root / /root
risks/questions: keep inverse zero/sign statements restricted to `(0,1)` so
  Mathlib's default-zero derivative at nondifferentiable clamp points is not
  misread as geometric curvature; place new forward results in Convexity
  rather than paying a root Differential invalidation
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
