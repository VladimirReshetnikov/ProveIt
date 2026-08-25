# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — exact forward and inverse curvature profile
branch/base: codex/fabius-both-papers merged with origin/main
  3d6cc72721129ba1fee040215c5cafa8adedbe0c in
  edc04fb9fa22153a73260f8b53e171965f081bbe
writing: none; workstream closed
reading: none
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
  repinned the primary article, walkthrough, and integration-frontier source
  claims to that code commit and rebuilt all three paired PDFs in three passes;
  committed the coherent documentation batch as
  `2127f5bb3e4bea1731301dbbc27d7eeaca21047e`; fetched and merged the latest
  origin/main, including its dyadic scale-zero and periodic/saddle refactors,
  without conflicts in `edc04fb9fa22153a73260f8b53e171965f081bbe`
validated: direct Lean elaboration and focused Lake builds pass for both
  `FabiusFunction.Convexity` (2661 jobs) and
  `FabiusFunction.FabiusInverse` (3248 jobs); the facade-only
  `/tmp/FabiusCurvatureFacadeAudit.lean` resolves every new declaration,
  passes `assert_no_sorry`, and reports exactly `[propext, Classical.choice,
  Quot.sound]`; all three final LaTeX logs were free of undefined/multiply
  defined references and errors, and rendered-text checks find the new names,
  exact pin, and no `??`; independent source/API and documentation audits pass;
  after the upstream merge, focused builds pass for
  `FabiusFunction.Convexity` (2661 jobs) and
  `FabiusFunction.FabiusInverse` (3248 jobs), the expanded facade audit again
  passes all 13 `assert_no_sorry` and exact-axiom checks, and
  `lake build +FabiusFunction` completes all 4008 jobs; both merge-parent
  `git diff --check` checks are clean
next: push the validated merge to main and codex/fabius-both-papers
lease: released 2026-08-25T15:40:31-07:00
git owner / build owner: /root / /root
risks/questions: keep inverse zero/sign statements restricted to `(0,1)` so
  Mathlib's default-zero derivative at nondifferentiable clamp points is not
  misread as geometric curvature; place new forward results in Convexity
  rather than paying a root Differential invalidation
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
