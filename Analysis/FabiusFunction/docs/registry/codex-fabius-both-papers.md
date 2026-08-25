# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — generic unit-Laplace moment bounds
branch/base: codex/fabius-both-papers synchronized with origin/main at
  1b2d7278785ad6ed92e856a80c19c2a3f6e48883
writing: none — generic unit-Laplace tranche integrated
reading: ProbabilityLaplaceMoments.lean, EndpointLaplaceComparison.lean
expected API: measure-generic midpoint log-convexity and tilt-subtraction
  factorial bounds for `unitLaplaceMoment`, plus bounded-Fabius corollaries;
  existing three-quarter canonical APIs become thin compatibility wrappers
completed: added the compactly-finite generic module, retained the established
  finite-measure and Fabius signatures as compatibility wrappers, removed the
  four private or inline power-times-exponential copies, registered the public
  module, and updated focused-import and audit bookkeeping
validated: direct elaboration of the new module; focused merged-source builds
  for `LaplaceMomentBounds`, `NegativeLaplaceDerivativeBounds`,
  `FabiusLambertDerivativeBounds`, `LaplacePeriodicSecondOrder`, and
  `NegativeLaplaceVerticalFourthBound`; 4008-job facade builds after both
  successive `origin/main` merges;
  facade-only `assert_no_sorry`, public-signature, and exact standard-axiom
  audit; independent mathematics, API, merge-resolution, import-DAG, and
  documentation review; three-pass rebuild of the 80-page primary PDF with no
  unresolved references; both index and worktree `git diff --check`
next: commit the rebuilt primary PDF and synchronized registry, then push both
  main and the feature branch by fast-forward
lease: released 2026-08-25T14:24:20-07:00
git owner / build owner: /root / /root
risks/questions: none — all six finite-measure compatibility names and both
  older Fabius three-quarter APIs retain their exact signatures
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
