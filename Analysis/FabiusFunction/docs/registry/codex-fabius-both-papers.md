# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — generic unit-Laplace moment bounds
branch/base: codex/fabius-both-papers synchronized with origin/main at
  bcdd6fe7203a011fd713b50cb9086de3f228d5d3
writing: UnitLaplaceMomentBounds.lean, LaplaceMomentBounds.lean,
  NegativeLaplaceDerivativeBounds.lean, FabiusLambertDerivativeBounds.lean,
  LaplacePeriodicSecondOrder.lean, NegativeLaplaceVerticalFourthBound.lean,
  Lean/FabiusFunction.lean, README.md, docs/AUDIT_FINDINGS.md,
  docs/registry/codex-fabius-both-papers.md
reading: ProbabilityLaplaceMoments.lean, EndpointLaplaceComparison.lean
expected API: measure-generic midpoint log-convexity and tilt-subtraction
  factorial bounds for `unitLaplaceMoment`, plus bounded-Fabius corollaries;
  existing three-quarter canonical APIs become thin compatibility wrappers
completed: added the compactly-finite generic module, retained the established
  finite-measure and Fabius signatures as compatibility wrappers, removed the
  four private or inline power-times-exponential copies, registered the public
  module, and updated focused-import and audit bookkeeping
validated: direct elaboration of the new module; focused current-source builds
  for `LaplaceMomentBounds`, `NegativeLaplaceDerivativeBounds`,
  `FabiusLambertDerivativeBounds`, `LaplacePeriodicSecondOrder`, and
  `NegativeLaplaceVerticalFourthBound`; a 4008-job facade build before the
  upstream-compatibility aliases; facade-only `assert_no_sorry` and standard
  axiom audit; independent mathematics, API, import-DAG, and documentation
  review; `git diff --check`
next: commit the local tranche, merge current `origin/main` at `f51777a18`,
  reconcile its overlapping Laplace generalizations through the compatibility
  wrappers, and rerun the facade audit before pushing
lease: held by /root from 2026-08-25T13:49:39-07:00 through
  2026-08-25T15:49:39-07:00
git owner / build owner: /root / /root
risks/questions: preserve all legacy canonical names and binder order; the
  generic midpoint theorem intentionally allows arbitrary real tilts
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
