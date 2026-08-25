# Workstream registry: `codex/fabius-theorem-polish-20260825`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: 10ef /root — theorem and exposition refinement campaign
branch/base: codex/fabius-theorem-polish-20260825 at published checkpoint
  26b3dc92dc5ee72b38fc85145aca614c53fb61dd, merging pinned origin/main
  72f80664131bc38be4dc68edefd75fca1a5c349a
writing: Lean/FabiusFunction/FabiusUniformSpline.lean and this registry file;
  no LaTeX or PDF path is leased
reading: the centered finite-spline probability API, its direct consumers,
  the all-real discrete-limit alternative, and active documentation status
expected API: an all-degree spline/CDF identification and range theorem,
  the exact right-saturation edge and endpoint value, plus shorter monotonicity
  and pointwise-convergence proofs; existing positive-degree API is preserved
completed: the initial Laplace-constant batch was independently reviewed and
  its exact 42-module import closure built serially; after origin/main exposed
  the same declarations together with a stronger generic abstraction and
  effective endpoint/cumulant bounds, the uncommitted duplicate was retired
  and pinned main was merged and published without source duplication
validated: all advertised origin heads fetched; no unmerged remote commit
  changes FabiusUniformSpline, and the only remote registry mention classifies
  it as read-only; all live worktrees were checked and none modifies the source
  file.  The 42-module Laplace build is pre-merge evidence only.  Post-merge
  validation is pending because c9a3 currently owns a contended Lake build.
next: implement and independently review the all-degree spline batch while
  remaining build-free; after the peer build exits, compile the exact focused
  closure one module per invocation and replay direct consumers
lease: FabiusUniformSpline source lease
  2026-08-25T14:46:11-07:00 through 15:46:11-07:00
git owner / build owner: /root / /root
risks/questions: worktrees C:/ProveIt, 8f3f, and c9a3 modify the primary
  exposition TeX/PDF or coverage map, while 8f3f and c9a3 also modify the
  walkthrough TeX/PDF.  Those documentation paths remain read-only here until
  their owners publish or release them; public Lean doc comments are in scope.
```

Source-only subagents remain read-only. They do not stage, commit, merge,
push, run Lean or Lake, or mutate caches and build outputs.
