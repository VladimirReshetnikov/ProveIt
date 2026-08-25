# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — effective dyadic cumulant constants
branch/base: codex/fabius-both-papers synchronized with origin/main at
  20b35c24005c8dddd7da3b475f487f52254f6a30
writing: none — effective-constant tranche complete
reading: DyadicSharpConditional.lean, EndpointLaplaceComparison.lean,
  FabiusSharpConstant.lean
expected API: pointwise `256/n` and `104448/n` normalized-moment estimates,
  a fully effective endpoint/Laplace logarithm comparison, and an explicit
  `2512945/(12n)` cumulant error bound for every `n >= 224043`
completed: exposed the two pointwise normalized-moment transfer constants,
  derived the effective endpoint and complete cumulant bounds, refactored the
  four legacy `IsBigO` results into compatibility wrappers, and documented
  the quantitative dyadic endpoint on the focused public import
validated: focused builds for `LaplaceMomentBounds` and
  `FabiusDyadicSharpCumulant`; full 4007-job facade build; facade-only
  `assert_no_sorry`, public-surface, and axiom audit; independent arithmetic,
  threshold, API, and documentation review; `git diff --check`
next: commit the effective-constant tranche, resynchronize with origin/main,
  and push by fast-forward
lease: released 2026-08-25T13:47:15-07:00
git owner / build owner: /root / /root
risks/questions: retain `n >= 224043` exactly; the threshold discharges the
  logarithm smallness condition and is not a cosmetic asymptotic cutoff
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
