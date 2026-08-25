# Workstream registry: `codex/fabius-theorem-polish-20260825`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: ebe4bd8442507df7b629aa87669fa6bb92e2f19e
HEAD and dirty paths: 4f36c5e58705d7dfe828955ab780d151392c4865
  after a conflict-free merge of fetched main; only this registry file is
  dirty for the present status reply
writing (exact paths): this registry file only; theorem-source edits are
  frozen and preserved in completed feature commits; no TeX, PDF,
  coordination, README, or root-aggregate path is leased
expected declarations or document claims: the frozen source tranche adds
  fabiusUniformSpline_eq_centeredPartialCDF_all,
  fabiusUniformSpline_mem_Icc_all,
  fabiusUniformSpline_eq_one_of_le,
  fabiusUniformSpline_one_eq_one,
  binary_telescope_tendsto_globalFabius_all,
  fabiusDiscreteLimitApproximationComplex_tendsto_binary_tsum_all, and
  fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum_all; it also
  simplifies all-degree monotonicity, convergence, and absolute-bound proofs
  while retaining the old nonnegative discrete-limit signatures as
  compatibility wrappers
completed commits: 504ab4055 (all-degree centered finite-spline probability
  API); b3bc48dfd (formalization-backed prose corrections); 3431ffdac
  (all-real discrete-limit series identifications); cbc5efd52 (merge fetched
  main 22d63a9f7 into the preserved feature checkpoint); 4f36c5e58 (refresh
  merge of fetched main ebe4bd844 immediately before publication)
validated (exact command, SHA/state, exit code): before the coordinator
  checkpoint was received, a named-mutex PowerShell harness ran
  `$env:LAKE_JOBS='1'; lake build "+FabiusFunction.<module>"` once per module
  over the dependency-first 52-module closure from FabiusFunction.Arithmetic
  through FabiusFunction.FabiusDiscreteLimitIntegration.  Every invocation
  exited 0 at HEAD b3bc48dfd plus the sole dirty path
  Lean/FabiusFunction/FabiusDiscreteLimitIntegration.lean; commit 3431ffdac
  preserves that exact source content.  This includes exit 0 for
  FabiusUniformSpline, its cheapest direct consumer FabiusComplexShiftSpline,
  and FabiusDiscreteLimitIntegration.  `git diff --check` exited 0, two
  independent hostile/API reviews found no blocker, and
  `python Analysis/FabiusFunction/scripts/doc_audit.py` exited 0 while
  reporting 159 inherited undocumented declarations in 17 other files.
not yet validated: merged HEAD 4f36c5e58 has not been compiled; the sole
  direct consumer PaperFabiusAsymptotic and root +FabiusFunction aggregate
  were not built.  No new validation will start without a board-assigned EVO
  build token.
requested integration or lease: review and integrate the isolated
  504ab4055 + b3bc48dfd spline tranche, and separately review 3431ffdac for
  the all-real discrete-limit endpoint API.  No additional write lease is
  requested.
conflicts / dependencies: both fetched-main merges were conflict-free but
  changed dependencies within both focused closures, so the successful
  pre-merge build is not merged-tip evidence.  Canonical exposition,
  walkthrough, frontier, coordination, README, and root aggregate remain
  frozen here.
next bounded step: commit and push this status reply to the feature branch,
  then wait read-only for coordinator integration review or an explicit build
  assignment.
```

Checkpoint published at 2026-08-25T16:00:47-07:00.  Source-only subagents
remained read-only: they did not stage, commit, merge, push, run Lean or Lake,
or mutate caches and build outputs.
