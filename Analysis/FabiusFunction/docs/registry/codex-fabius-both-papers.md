# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — inverse curvature strengthening
branch/base: codex/fabius-both-papers synchronized with origin/main at
  35852aa65ba66cf700419c296a78460b02bb65b3
writing: none — workstream closed
reading: Convexity.lean, Differential.lean, Monotonicity.lean,
  InverseNotElementary.lean
expected API: exact reciprocal-cubic second derivative and strict
  concavity/convexity on the two closed halves of the unit interval
completed: merged origin/main through 35852aa65; combined its exact global
  smoothness and all-order endpoint-steepness APIs with the reciprocal-cubic
  and closed-half curvature family; retained the exact-Lean primary exposition
  and synchronized its rebuilt PDF
validated: focused Lake module build (2832 jobs), full facade build (4007
  jobs), facade-only no-sorry/axiom audit, independent source and document
  reviews, and three-pass rebuilt/visually inspected PDFs
next: none — merge workstream complete
lease: released 2026-08-25T13:12:59-07:00
git owner / build owner: /root / /root
risks/questions: preserve endpoint claims—the inverse calculus is interior,
  while the closed-half shape theorems use continuity and differentiate only
  on interval interiors
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
