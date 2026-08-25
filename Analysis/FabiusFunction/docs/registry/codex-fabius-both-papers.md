# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — inverse curvature strengthening
branch/base: codex/fabius-both-papers at 783cecf7208edd4de86fd0cee7d4b9f13299ee60
writing: Lean/FabiusFunction/FabiusInverse.lean; README.md; the inverse
  Missing Parts TeX/PDF pairs; docs/fabius_lean_walkthrough TeX/PDF;
  this registry file
reading: Convexity.lean, Differential.lean, Monotonicity.lean,
  InverseNotElementary.lean
expected API: exact reciprocal-cubic second derivative and strict
  concavity/convexity on the two closed halves of the unit interval
completed: merged origin/main through 783cecf72; integrated the theorem family
  and synchronized the inverse documentation
validated: direct Lean source, focused Lake module build, independent source
  review, and rebuilt/visually inspected PDFs; axiom harness pending
next: complete the axiom/facade and downstream audits, commit, and publish
lease: 2026-08-25T11:40:11-07:00 until this bounded tranche is committed or
  the next synchronization checkpoint
git owner / build owner: /root / /root
risks/questions: preserve endpoint claims—the inverse calculus is interior,
  while the closed-half shape theorems use continuity and differentiate only
  on interval interiors
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
