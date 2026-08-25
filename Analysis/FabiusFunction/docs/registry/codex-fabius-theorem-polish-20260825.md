# Workstream registry: `codex/fabius-theorem-polish-20260825`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: 10ef /root — theorem and exposition refinement campaign
branch/base: codex/fabius-theorem-polish-20260825 at published checkpoint
  61928eb0d0f448f997a53c52d8154dfb9f16450d, based on origin/main
writing: Lean/FabiusFunction/LaplaceMomentBounds.lean and this registry file;
  no LaTeX or PDF path is leased
reading: direct consumers of the dyadic Laplace-moment bounds and the active
  documentation worktrees' status only
expected API: explicit thresholded bounds
  dyadicEndpointSecondOrder_sq_le with constant 256 and
  dyadicHigherLaplaceMoments_le with constant 104448; the existing IsBigO
  declarations become compatibility corollaries with unchanged signatures
completed: feature branch and initial survey registry published; three
  independent read-only surveys found no advertised-branch overlap for the
  selected leaf module
validated: every advertised origin head fetched and no host-wide Lean, Lake,
  Elan, or PDFLaTeX process was running at the claim time; a subsequent full
  worktree audit found an unadvertised modified HalfQBinomial file in 8f3f,
  correcting the narrower initial path check before any production edit;
  unchanged-tree +FabiusFunction.HalfQBinomial baseline built successfully
  (2,020 jobs), and all 12 worktrees were then checked for the replacement
  source and documentation paths
next: extract the two pointwise inequalities from the existing IsBigO proofs,
  independently review the exact constants and n >= 2 boundary, then build
  +FabiusFunction.LaplaceMomentBounds and a focused downstream consumer
lease: LaplaceMomentBounds source lease refreshed
  2026-08-25T13:54:35-07:00 through 14:54:35-07:00
git owner / build owner: /root / /root
risks/questions: all 12 live worktrees were checked before this replacement
  claim and none modifies LaplaceMomentBounds; worktrees 8f3f and c9a3 both
  modify the walkthrough TeX/PDF, so those documentation paths remain read-
  only here until their owners publish or release them
```

Source-only subagents remain read-only. They do not stage, commit, merge,
push, run Lean or Lake, or mutate caches and build outputs.
