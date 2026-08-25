# Workstream registry: `codex/fabius-both-papers`

**Status: closed historical.** The completed work entered `origin/main` through
exact tip `f51777a184240e20d5991676ebb3465b0824b942` and is incorporated by the
current theorem-refinements merge.  The released leases below are provenance,
not live Git or build authority.

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — effective dyadic cumulant constants
branch/base: codex/fabius-both-papers integrated into origin/main at
  f51777a184240e20d5991676ebb3465b0824b942
writing: none — effective-constant tranche complete
reading: DyadicSharpConditional.lean, EndpointLaplaceComparison.lean,
  FabiusSharpConstant.lean
expected API: pointwise `256/n` and `104448/n` normalized-moment estimates,
  a fully effective endpoint/Laplace logarithm comparison, and an explicit
  `2512945/(12n)` cumulant error bound for every `n >= 224043`
completed: exposed the two pointwise normalized-moment transfer constants,
  derived the effective endpoint and complete cumulant bounds, refactored the
  four legacy `IsBigO` results into compatibility wrappers, and documented
  the quantitative dyadic endpoint on the focused public import; merged
  origin/main through `721260e0e` and retained the complete theorem family
validated: focused builds for `LaplaceMomentBounds` and
  `FabiusDyadicSharpCumulant`; historical aggregate facade evidence at
  5f6d0ab4b8b2e9ab472831ba5dd8c9e467cb1755; facade-only `assert_no_sorry`,
  public-surface, and axiom audits; independent arithmetic, threshold, API,
  and documentation review; `git diff --check`.  The historical aggregate
  predates 13 final incoming Lean-file changes and is not evidence for exact
  tip f51777a1 or its later union
next: none — registry closed after integration
lease: released 2026-08-25T13:47:15-07:00
git owner / build owner: none / none (released historical lease)
risks/questions: retain `n >= 224043` exactly; the threshold discharges the
  logarithm smallness condition and is not a cosmetic asymptotic cutoff
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
