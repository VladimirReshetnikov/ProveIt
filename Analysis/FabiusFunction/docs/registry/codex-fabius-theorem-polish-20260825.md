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

## Coordinator integration disposition

Approved for integration after an independent theorem/API review and
immutable merged-tip validation at `60458909abc2762e47d071dcc6ed8f3812021ffd`
(parents `4c6bbac41f987e171f8d15a0b1aa842d1e3ee847` and
`1772688b98b44be42095c14b9ccab3c339935242`).  The review found no truth,
signature-compatibility, duplication, registry, or merge blocker.  In
particular, the three old nonnegative discrete-limit theorem signatures are
preserved exactly as compatibility wrappers, while the new `_all` theorems
correctly cover every real input.

With the codexbox build token held and `LAKE_JOBS=1`, each of the following
one-target invocations exited 0 at that immutable merge commit:

```text
lake build +FabiusFunction.FabiusUniformSpline
lake build +FabiusFunction.FabiusDiscreteLimitIntegration
lake build +FabiusFunction.FabiusComputability
lake build +FabiusFunction.PaperFabiusAsymptotic
```

`git diff --check` also exited 0, and the two edited Lean files contain no
`sorry`, `admit`, `axiom`, or `opaque`.  The earlier registry sentence that
the merged tip had not been compiled is retained above as an accurate record
of the worker's checkpoint state and is superseded by this disposition.

## Next ordinary claim: all-real normalized Laplace moments

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 12e7137a897b8ec99ddf8935f64fff9f35977617
HEAD and dirty paths: 12e7137a897b8ec99ddf8935f64fff9f35977617
  after a clean fast-forward from 1772688b9; only this registry file is dirty
  for the present claim, and no theorem or document source has been edited
writing (exact paths): this registry file only at this coordination checkpoint;
  the proposed next ordinary claim is limited to
  Lean/FabiusFunction/NegativeLaplace.lean,
  Lean/FabiusFunction/LaplaceMoments.lean,
  Lean/FabiusFunction/NegativeLaplaceDerivatives.lean, and
  Lean/FabiusFunction/NegativeLaplaceVertical.lean; no TeX, PDF, README,
  aggregate, primary-exposition, walkthrough, frontier, or coordination path
  is claimed
expected declarations or document claims: preserve the exact public
  signatures of generatingFunction_neg_pos and
  fabiusLaplaceMoment_zero_pos while relocating them to their upstream-most
  natural modules; add one_le_generatingFunction_of_nonneg,
  generatingFunction_pos, fabiusLaplaceMoment_zero_pos_all,
  normalizedLaplaceMoment_zero_all,
  normalizedLaplaceMoment_hasDerivAt_all,
  deriv_normalizedLaplaceMoment_all,
  contDiff_normalizedLaplaceMoment, and
  continuous_normalizedLaplaceMoment; remove the now-redundant downstream
  positivity proofs and make the positive-half-line continuity result a
  compatibility corollary of global continuity
completed commits: the prior theorem-polish tranche is integrated through
  301a46561 and independently validated at 60458909a; this branch has only
  fast-forwarded to the live-board commit 12e7137a for the new claim, so no
  source checkpoint exists yet
validated (exact command, SHA/state, exit code): coordinator evidence on
  fetched main records `LAKE_JOBS=1 lake build +FabiusFunction` at immutable
  9887ea584, all 4008 jobs completed, exit 0; subsequent changes through
  12e7137a do not alter the Lean tree; three independent read-only audits of
  the proposed tranche found an acyclic placement and no mathematical or API
  blocker, but they are preflight evidence rather than compiler validation
not yet validated: every proposed declaration above; no Lean, Lake, TeX, PDF,
  or cache-mutating command was launched, because the EVO build token remains
  unavailable to this branch
requested integration or lease: advertise the exact four ordinary source
  paths above as a nonoverlapping claim; no serialized path is requested;
  request an EVO Lean build token only after a coherent source checkpoint is
  available for focused validation
conflicts / dependencies: the claim deliberately consolidates two identical
  positivity proofs now split between NegativeLaplaceDerivatives and
  NegativeLaplaceVertical; canonical exposition and coverage synchronization
  remain deferred to their document owner while those paths are frozen; the
  separate finite-q dependence witness discovered during reconnaissance is
  not part of this claim
next bounded step: push this registry-only claim, re-read the fetched board
  and audit every advertised registry/tip for path or declaration overlap;
  preserve a read-only source state until the current coordination stop is
  explicitly released, and launch no validation without the board token
```

Claim published at 2026-08-25T17:18:35-07:00.  Subagents remained read-only:
they did not edit, stage, commit, merge, push, run Lean or Lake, or mutate
caches and build outputs.

## All-real Laplace source checkpoint

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: e18f5d0b0e3ec78e2b14e7006af6c7e916b42923
HEAD and dirty paths: 87c9b00f4dc7e0f6e69c22db3dc8c07f6ccf13e7;
  source is clean and only this registry file is dirty for the status reply
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/NegativeLaplace.lean,
  Lean/FabiusFunction/LaplaceMoments.lean,
  Lean/FabiusFunction/NegativeLaplaceDerivatives.lean, and
  Lean/FabiusFunction/NegativeLaplaceVertical.lean; this reply writes only
  docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims: generatingFunction_neg_pos and
  fabiusLaplaceMoment_zero_pos retain their exact public signatures in more
  upstream modules; new one_le_generatingFunction_of_nonneg,
  generatingFunction_pos, fabiusLaplaceMoment_zero_pos_all,
  normalizedLaplaceMoment_zero_all,
  normalizedLaplaceMoment_hasDerivAt_all,
  deriv_normalizedLaplaceMoment_all,
  contDiff_normalizedLaplaceMoment, and
  continuous_normalizedLaplaceMoment establish positivity and smooth quotient
  calculus on the whole real line; the old positive-scale normalized APIs
  remain compatibility wrappers
completed commits: 87c9b00f4 (four-file all-real Laplace source checkpoint),
  based on clean merge 5f1b35c90 of acknowledged board main e18f5d0b0;
  prior registry claim ca387fea0 and synchronization merge 8e4862b2b are
  already pushed
validated (exact command, SHA/state, exit code): no compiler validation is
  claimed; `git diff --check` exited 0 before commit, the exact four changed
  files had no `sorry`, `admit`, `axiom`, or `opaque`, and three independent
  hostile source reviews checked Mathlib signatures, import reachability,
  public binder compatibility, duplicate names, proof regimes, and prose
  domain claims without finding a blocker
not yet validated: 87c9b00f4 has not been elaborated; no Lean, Lake, TeX, PDF,
  Python audit, or cache-mutating command was launched because no EVO build
  token is assigned to this branch
requested integration or lease: request coordinator review of 87c9b00f4 and
  a serialized EVO token for one-target builds, in topological order, of
  +FabiusFunction.NegativeLaplace, +FabiusFunction.LaplaceMoments,
  +FabiusFunction.NegativeLaplaceDerivatives, and
  +FabiusFunction.NegativeLaplaceVertical, followed if requested by the cheap
  direct consumer +FabiusFunction.FabiusSaddleReduction; request no document
  or serialized-path lease
conflicts / dependencies: current board e18f5d0b0 explicitly acknowledges
  this four-path claim and reports no competitor; the canonical exposition,
  walkthrough, PAPER_COVERAGE, frontier, README, coordination files, and root
  aggregate remain untouched; future document-owner synchronization should
  state all-real G positivity, M_0 positivity, normalized smoothness, and the
  quotient recurrence while retaining the positive-scale domain of the
  negative-Laplace product logarithm
next bounded step: commit and push this registry reply with 87c9b00f4, then
  keep the source frozen for coordinator review and token-assigned validation;
  do not launch any build or edit a human-document path meanwhile
```

Source checkpoint recorded at 2026-08-25T17:36:09-07:00.  Three subagents
implemented disjoint leased files and then independently reviewed the combined
tranche; none staged, committed, merged, pushed, or ran a validation process.

## Follow-on ordinary claim: normalized-moment nonnegativity

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: e18f5d0b0e3ec78e2b14e7006af6c7e916b42923
HEAD and dirty paths: 1d4a88a42f9ab886ec0b296bbfc684209e871abc;
  the published all-real Laplace source remains clean and frozen, and only
  this registry file is dirty for the follow-on claim
writing (exact paths): this claim initially writes only this registry file;
  the proposed independent follow-on is limited to
  Lean/FabiusFunction/LaplaceMomentBounds.lean
expected declarations or document claims: add
  normalizedLaplaceMoment_nonneg_all, proving
  0 <= normalizedLaplaceMoment F k s for every natural k and real s from the
  already-global raw-moment nonnegativity theorem; preserve the exact name,
  binders, statement, and proof of normalizedLaplaceMoment_nonneg while
  documenting it as the positive-scale compatibility form
completed commits: 87c9b00f4 and registry report 1d4a88a42 are pushed and
  remain the immutable preceding tranche; no follow-on source commit exists
validated (exact command, SHA/state, exit code): read-only dependency review
  found that the proposed proof needs only normalizedLaplaceMoment and
  fabiusLaplaceMoment_nonneg already present before 87c9b00f4, introduces no
  import, and is a direct application of div_nonneg; this is static review,
  not compiler evidence
not yet validated: no follow-on source has been written or elaborated; no
  Lean, Lake, TeX, PDF, Python audit, or cache-mutating command will start
  without the EVO token
requested integration or lease: advertise the one ordinary source path and
  declaration above; request no serialized or document path and no immediate
  build token
conflicts / dependencies: a read-only scan of all locally advertised Fabius
  refs and registries found no competing declaration or live claim for
  LaplaceMomentBounds.lean; the theorem is logically independent of the
  unvalidated preceding checkpoint, although this branch history descends
  from it; all frozen paths and the finite-q witness remain excluded
next bounded step: push this registry-only claim, fetch/read the board, repeat
  the advertised-tip collision scan, and only then edit the single claimed
  source file; checkpoint it explicitly as not compiled
```

Follow-on claim published at 2026-08-25T17:45:06-07:00.
