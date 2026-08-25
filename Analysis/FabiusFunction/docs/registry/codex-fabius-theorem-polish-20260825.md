# Workstream registry: `codex/fabius-theorem-polish-20260825`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: 10ef /root — theorem and exposition refinement campaign
branch/base: codex/fabius-theorem-polish-20260825 at published checkpoint
  61928eb0d0f448f997a53c52d8154dfb9f16450d, based on origin/main
writing: Lean/FabiusFunction/HalfQBinomial.lean and this registry file
reading: the primary synthesis q-binomial section, effective-constant sites,
  and probability/discrete-limit leaf modules
expected API: a general finite-q-Pochhammer zero-factor characterization;
  the exact roots 1, 2, ..., 2^(n-1) at q = 1/2; and q-binomial-polynomial
  corollaries in both native and literal notation
completed: feature branch and initial survey registry published; three
  independent read-only surveys found no advertised-branch overlap for the
  selected leaf module
validated: every advertised origin head fetched; exact-path remote-branch and
  sibling-worktree dirty-state checks found no HalfQBinomial writer; no host-
  wide Lean, Lake, Elan, or PDFLaTeX process was running at the claim time
next: prototype the factor/root equivalences, obtain an independent source
  review, then run the focused HalfQBinomial target under the single build lane
lease: refreshed 2026-08-25T13:48:39-07:00 through 14:48:39-07:00
git owner / build owner: /root / /root
risks/questions: the primary synthesis is actively conflicted in worktree c9a3
  and remains read-only here until that owner publishes or releases it; no
  documentation merge will be attempted behind that writer
```

Source-only subagents remain read-only. They do not stage, commit, merge,
push, run Lean or Lake, or mutate caches and build outputs.
