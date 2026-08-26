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

## Normalized-moment nonnegativity source checkpoint

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: e18f5d0b0e3ec78e2b14e7006af6c7e916b42923
HEAD and dirty paths: efee2a7e16c891e70094ef00479df8d3d8ea05a4;
  the five source files are clean and only this registry file is dirty for
  the status reply
writing (exact paths): completed follow-on writes only
  Lean/FabiusFunction/LaplaceMomentBounds.lean; this reply writes only
  docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims: normalizedLaplaceMoment_nonneg_all
  now proves 0 <= normalizedLaplaceMoment F k s for every natural k and real
  s; normalizedLaplaceMoment_nonneg retains its exact positive-scale public
  signature and proof while its comment identifies the compatibility role
completed commits: efee2a7e1 (one-file all-real normalized nonnegativity),
  following source checkpoint 87c9b00f4 and registry tip a6091bacf
validated (exact command, SHA/state, exit code): no compiler validation is
  claimed; `git diff --check` exited 0, the changed file contains no `sorry`,
  `admit`, `axiom`, or `opaque`, and two independent read-only proof/prose
  reviews found no truth, placement, import, signature, or documentation
  blocker
not yet validated: efee2a7e1 and its dependency 87c9b00f4 have not been
  elaborated; no Lean, Lake, TeX, PDF, Python audit, or cache-mutating command
  was launched because no EVO build token is assigned
requested integration or lease: review efee2a7e1 with 87c9b00f4 and append
  +FabiusFunction.LaplaceMomentBounds to the previously requested serialized
  one-target validation sequence; request no additional source or document
  lease
conflicts / dependencies: the post-claim scan of all advertised Fabius refs
  found no competitor for the path or declaration; although an initial static
  design could use raw nonnegativity for both quotient arguments independently
  of 87c9b00f4, the final proof intentionally uses
  fabiusLaplaceMoment_zero_pos_all so the formal proof records that the
  denominator is genuinely nonzero, matching the human meaning of
  normalization
next bounded step: commit and push this registry reply with efee2a7e1, then
  freeze all five source paths for coordinator review and token-assigned
  validation; do not launch a build or enter frozen document paths
```

Follow-on source checkpoint recorded at 2026-08-25T17:48:42-07:00.

## Coordination freeze after the source checkpoints

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: e18f5d0b0e3ec78e2b14e7006af6c7e916b42923
HEAD and dirty paths: 5331c74d53c6af3d128fd6365923e83b57187611;
  all theorem-source paths are clean and frozen, and only this registry file
  is dirty for the present status reply
writing (exact paths): this registry file only; no additional Lean, TeX, PDF,
  README, aggregate, exposition, walkthrough, frontier, or coordination path
  will be edited before a new board assignment
expected declarations or document claims: no new claim; preserve the four-file
  all-real Laplace checkpoint at 87c9b00f4 and the already-pushed one-file
  normalized-nonnegativity follow-on at efee2a7e1 without expanding either
completed commits: 87c9b00f4 (all-real Laplace source), 1d4a88a42 (source
  report), a6091bacf (one-file follow-on claim), efee2a7e1 (all-real normalized
  nonnegativity), and 5331c74d5 (follow-on source report)
validated (exact command, SHA/state, exit code): no compiler validation is
  claimed; the source commits have only the static checks reported above,
  including clean `git diff --check` results and hostile read-only reviews
not yet validated: neither 87c9b00f4 nor efee2a7e1 has been elaborated; no
  Lean, Lake, TeX, PDF, Python audit, or cache-mutating validation process has
  been launched on this branch
requested integration or lease: coordinator review of both preserved source
  commits and, only when explicitly assigned, serialized focused Lean builds;
  no new path lease is requested
conflicts / dependencies: the live board at e18f5d0b0 explicitly acknowledges
  the original four-source tranche but does not yet acknowledge the later
  LaplaceMomentBounds.lean follow-on; that already-pushed follow-on is therefore
  frozen for coordinator disposition, with no further source work or validation
next bounded step: push this registry-only freeze report to the feature branch,
  then wait read-only for a coordinator checkpoint; do not push `main`, do not
  force-push, and do not start a build without the applicable host token
```

Freeze status recorded after the 2026-08-25 17:21 PDT board was re-read from
`origin/main`.  The feature tip remained clean, contained current main as an
ancestor, and matched its remote tracking branch before this registry-only
reply.

## Read-only proof and reciprocity audit under the freeze

Three independent read-only reviews examined the preserved five-source
checkpoint, all advertised Fabius branch tips available after the latest
fetch, and the canonical human-readable Laplace/discrete-limit statements.
They did not edit production source, run Lean, Lake, TeX, PDF, or Python
validation, or mutate Git state.

### Proof preflight

No definite elaboration blocker was found.  The reviews checked the actual
Mathlib signatures of `intervalIntegral.integral_nonneg`, `ContDiff.div`, and
`HasDerivAt.deriv`; the transitive import paths of both relocated declarations;
the `ContDiff` scoped infinity notation; every public binder preserved by the
compatibility wrappers; and uniqueness of all eleven new or relocated names.

The fifth-file theorem `normalizedLaplaceMoment_nonneg_all` intentionally uses
`fabiusLaplaceMoment_zero_pos_all`.  It is therefore a consumer of the first
four-file tranche, not an independently validatable checkpoint.  Its focused
build belongs after `NegativeLaplace`, `LaplaceMoments`, and
`NegativeLaplaceDerivatives` in the requested serialized sequence.  Although
raw zeroth-moment nonnegativity would suffice for `div_nonneg`, retaining the
strictly positive denominator records why the quotient is an honest
normalization rather than an artifact of totalized division.

### Human-readable claims that need correction or formalization

1. The walkthrough at lines 1491 and 1523--1525, the primary exposition at
   lines 2754--2758, `PAPER_COVERAGE.md` line 168, and the glossary's
   `complex-shift` and `q-discrete-limit` entries assert that a finite
   discrete-limit row can genuinely depend on the shift and, in several
   places, that this is explicitly formalized.  Current main proves that every
   fixed shift has the same limit but contains no theorem exhibiting unequal
   finite rows.  The primary and glossary additionally say the discrete row
   and global-series construction are not termwise identical, for which there
   is likewise no named finite-index inequality.  Until a witness is proved,
   the accurate statement is that finite rows retain the shift parameter and
   Lean proves independence only in the limit; no finite-row independence or
   nonconstancy theorem, and no termwise identity, is currently asserted.

2. The walkthrough at lines 1888--1892 calls
   `normalizedLaplaceMoment F 1 s = -L'(s)` exact without side conditions.
   Algebraically, `negativeLaplaceLogFirst F s` is globally defined as the
   negative of the first normalized moment.  Its identification with the
   derivative of the actual negative-Laplace product logarithm is proved only
   for `0 < s`, by `negativeLaplaceLog_hasDerivAt`.  The global quotient APIs
   in `87c9b00f4` deliberately do not enlarge that logarithmic domain.

3. Current main already proves, but the primary exposition does not state as a
   coherent theorem, the all-real raw-moment package
   `fabiusLaplaceMoment_nonneg`, `fabiusLaplaceMoment_hasDerivAt`, and
   `contDiff_fabiusLaplaceMoment`: respectively `M_k(s) >= 0`,
   `M_k'(s) = -M_(k+1)(s)`, and `M_k` smooth on all of `Real`.  The current-main
   positive-scale normalized APIs are also substantially underdocumented.

4. The primary complex discrete-limit theorem has the right all-real meaning
   but omits adjacent mappings to
   `fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all`, the two
   all-real `tsum` endpoints, the weighted-shift-spline identity, and the
   Toeplitz mass/variation declarations.  Its fixed-cutoff Taylor lemma also
   lacks adjacent mappings to
   `fabiusComplexShiftSpline_sub_center_eq_taylorBranches`,
   `normalizedThueMorseSplineBranch_center_eq_uniformSpline`, and
   `norm_normalizedThueMorseSplineBranch_center_le_one`.

### Exact future reciprocity handoff

After `87c9b00f4` and `efee2a7e1` are compiled and integrated, the document
owner can add one compact theorem after the primary probability--Laplace
bridge.  With `M_k(s)` the raw tilted moments and `R_k(s)=M_k(s)/M_0(s)`, it
should state for all natural `k` and real `s`:

- `M_k(s) >= 0`, `M_0(s) = G(-s) > 0`,
  `M_k'(s) = -M_(k+1)(s)`, and `M_k` is smooth;
- `R_0(s) = 1`, `R_k(s) >= 0`, and `R_k` is smooth; and
- `R_k'(s) = -R_(k+1)(s) + R_k(s) R_1(s)`.

The exact branch-only names are
`one_le_generatingFunction_of_nonneg`, `generatingFunction_pos`,
`fabiusLaplaceMoment_zero_pos_all`, `normalizedLaplaceMoment_zero_all`,
`normalizedLaplaceMoment_nonneg_all`, `contDiff_normalizedLaplaceMoment`,
`continuous_normalizedLaplaceMoment`,
`normalizedLaplaceMoment_hasDerivAt_all`, and
`deriv_normalizedLaplaceMoment_all`.  They remain uncompiled feature-branch
artifacts and must not yet be described as proved current-main results.  The
human theorem must end with the explicit warning that the product-logarithm
and cumulant-derivative identifications remain restricted to `s > 0`.

The smallest exact repair for finite-stage dependence is still excluded from
this branch's live tranche: in
`FabiusDiscreteLimitToeplitz.lean`, prove the depth-one identity
`fabiusDiscreteLimitApproximationReal q (1 / 3) 1 =
q ^ 2 / 2 - q / 3 + 2 / 9`, then derive the unequal values `2 / 9` and
`7 / 18` at `q = 0` and `q = 1`.  No advertised tip contains that theorem and
no active registry claims the file, but this branch will not write it unless a
later board checkpoint releases the present bounded tranche and a new exact
claim is published first.

## Synchronization with coordinator checkpoint `148990f0a`

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 148990f0a2a9b665edaf3394656be1e7c46caf7e
HEAD and dirty paths: ba1ba2a72c9b249926d7d2b6e81cf17a90024406;
  conflict-free merge of fetched main is committed, all claimed theorem
  sources are clean and frozen, and only this registry file is dirty for the
  present status reply
writing (exact paths): this registry file only; no new source or human-document
  path is added, in accordance with the exact branch instruction on the live
  board
expected declarations or document claims: no new claim; preserve the
  four-file all-real Laplace tranche at 87c9b00f4, its dependent
  LaplaceMomentBounds follow-on at efee2a7e1, and the read-only reciprocity
  handoff at d1ce004d4
completed commits: 87c9b00f4 (four-source checkpoint), efee2a7e1 (dependent
  normalized-nonnegativity checkpoint), d1ce004d4 (proof/reciprocity audit),
  and ba1ba2a72 (conflict-free merge of coordinator main 148990f0a)
validated (exact command, SHA/state, exit code): no validation of this branch's
  Lean delta is claimed; `git merge-tree` found no conflict before the merge,
  the merge completed without conflict, `git diff --check` exited 0, and
  `git merge-base --is-ancestor origin/main HEAD` exited 0 at ba1ba2a72
not yet validated: 87c9b00f4 and efee2a7e1 remain unelaborated; no Lean, Lake,
  TeX, PDF, Python audit, or cache-mutating process was launched on EVO because
  the board grants no token to this branch
requested integration or lease: finish the independent theorem/API review;
  if approved, validate the four-file dependency tranche first and
  +FabiusFunction.LaplaceMomentBounds afterward under an explicitly assigned
  host token; no additional path lease is requested
conflicts / dependencies: main's natural-knot/coordination delta touched only
  AGENTS.md, README.md, GlobalExtension.lean, the both-papers registry, and the
  coordinator board, so it was disjoint from this branch's five claimed source
  paths and own registry; the new board explicitly acknowledges the fifth-file
  dependency and freezes all five paths under review
next bounded step: push this registry-only post-merge report to the feature
  branch, then hold all source steady and poll read-only for the review or
  token disposition; do not push main and do not start validation unassigned
```

Post-merge status prepared immediately after the board at `148990f0a` was read
from fetched `origin/main`.

## Coordinator disposition at `15b922326`

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 15b922326a51e47e2462f512f5c68c8b70b3816a
HEAD and dirty paths: afa544674ee97f14ad7c5eb749ad83052955ac91;
  the worktree was clean before this registry-only disposition reply, and only
  this registry file is now being written
writing (exact paths): this registry file only; no source, TeX, PDF, README,
  aggregate, coverage, audit, exposition, walkthrough, frontier, or
  coordination path is being changed
expected declarations or document claims: no new claim; the five-source
  all-real Laplace tranche is complete on main, its leases are released, and
  the finite-depth discrete-limit opportunities below remain unclaimed
completed commits: feature source checkpoints 87c9b00f4 and efee2a7e1;
  coordinator integration 0d308188c; narrow coordinator elaboration repair
  c4bc42f16; current main records the completed tranche through 301a46561
validated (exact command, SHA/state, exit code): coordinator-owned serialized
  builds, not runs from this feature worktree: at 0d308188c,
  +FabiusFunction.NegativeLaplace and +FabiusFunction.LaplaceMoments both
  exited 0; the first +FabiusFunction.NegativeLaplaceDerivatives attempt
  exited 1 and is not evidence; after the pointwise-quotient ContDiff repair
  at c4bc42f16, +FabiusFunction.NegativeLaplaceDerivatives,
  +FabiusFunction.NegativeLaplaceVertical,
  +FabiusFunction.LaplaceMomentBounds, and
  +FabiusFunction.PaperFabiusAsymptotic each exited 0
not yet validated: this feature tip itself was never elaborated and retains
  the pre-repair ContDiff proof; no Lean, Lake, TeX, PDF, Python audit, or
  cache-mutating process was launched on EVO in this checkpoint
requested integration or lease: none; the tranche is integrated, all five
  leases are released, and this branch has no EVO build token
conflicts / dependencies: no merge was attempted after fetching 15b922326;
  current main contains the accepted repair and supersedes the unelaborated
  proof at this feature tip; there are no dirty source paths to preserve
next bounded step: commit and push this registry-only disposition to the
  feature branch, then keep the write set frozen; do not push main, do not
  force-push, and do not launch validation without an explicit host token
```

Two final source-only reviews completed before this disposition and made no
repository changes.  They independently confirmed the proposed finite-stage
translation witness
`fabiusDiscreteLimitApproximationReal q (1 / 3) 1 =
q ^ 2 / 2 - q / 3 + 2 / 9`, hence the unequal specializations `2 / 9` and
`7 / 18` at `q = 0` and `q = 1`.  They also sharpened the separate prose claim
about finite approximants: with the existing `Finset.range (N + 1)` convention,
the discrete row at `q = 0`, `x = 1 / 3`, depth `1` is `2 / 9`, whereas the
binary (and therefore global-q) partial sum through scale `1` is `0`.  The
global-q and binary summands themselves are termwise equal by
`qBinomialFabiusGlobalSummand_eq`; only the same-depth discrete row differs.
These are uncompiled proof plans, not new claims or validation evidence, and
must be advertised in exact nonoverlapping source paths before any future
implementation.

## Coordinator all-real Laplace integration disposition

The five-source tranche is accepted after independent theorem/API/dependency
review and serialized validation.  The review found no mathematical,
signature-compatibility, import-cycle, duplicate, or scope blocker.  Source
checkpoint `87c9b00f4` supplies the four-file global positivity and smooth
normalized-moment API; dependent checkpoint `efee2a7e1` supplies the all-real
normalized nonnegativity theorem.  The later feature commits through
`d1ce004d4` change only this registry.

Coordinator merge `0d308188c` exposed one elaboration-only defect in
`contDiff_normalizedLaplaceMoment`: `simpa` did not identify the pointwise
quotient with the named definition under the inferred normed-space instance.
Commit `c4bc42f16` fixes it by changing the goal explicitly to the lambda
quotient before applying `ContDiff.div`; the theorem statement and mathematics
are unchanged.

With the sole codexbox token and `LAKE_JOBS=1`, these separate one-target
invocations supplied the final evidence:

```text
lake build +FabiusFunction.NegativeLaplace             # 2831 jobs, exit 0
lake build +FabiusFunction.LaplaceMoments              # 2857 jobs, exit 0
lake build +FabiusFunction.NegativeLaplaceDerivatives  # 2858 jobs, exit 0 after c4bc42f16
lake build +FabiusFunction.NegativeLaplaceVertical     # 3194 jobs, exit 0
lake build +FabiusFunction.LaplaceMomentBounds         # 3417 jobs, exit 0
lake build +FabiusFunction.PaperFabiusAsymptotic       # 3957 jobs, exit 0
```

The first derivative-module attempt at merge `0d308188c` exited 1 with the
folding mismatch described above and is not validation evidence.  The first
two green targets' edited source blobs are unchanged at `c4bc42f16`; every
target from the repaired derivative module onward ran at that immutable tree.
`git diff --check` passes and the five edited sources contain no `sorry`,
`admit`, `axiom`, or `opaque`.  All five source leases are released.

## Claim: finite-depth shift dependence and asymptotic independence

Claim advertised at 2026-08-25 18:49 PDT after fetching and merging
`origin/main` `383bc967268df018cc0bc1634b997114863c1658` into the clean
feature branch.  A current-main and all-advertised-tip path audit found that no
branch changes either claimed source after its merge base, no active registry
leases either path, and no existing declaration or plausible alternate name
implements this package.  This claim promotes the source-only handoff above;
it does not present the finite-depth witness as a newly discovered idea.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 383bc967268df018cc0bc1634b997114863c1658
HEAD and dirty paths: 8fb9d79de2974ffc41f5c602ca6023669259de8a;
  clean before this registry-only exact-path claim
writing (exact paths):
  Lean/FabiusFunction/FabiusDiscreteLimitToeplitz.lean;
  Lean/FabiusFunction/FabiusDiscreteLimitIntegration.lean;
  this branch registry
expected declarations or document claims:
  fabiusDiscreteLimitApproximation_one_third_depth_one;
  fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one;
  fabiusDiscreteLimitApproximationReal_one_one_third_depth_one;
  fabiusDiscreteLimitApproximationReal_zero_ne_one_at_one_third_depth_one;
  fabiusDiscreteLimitApproximationComplex_sub_tendsto_zero_all;
  fabiusDiscreteLimitApproximationReal_sub_tendsto_zero_all;
  fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one_ne_binaryPartialSum;
  fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one_ne_qBinomialPartialSum;
  source-level prose will distinguish (i) genuine finite-row q-dependence,
  (ii) pairwise asymptotic shift-independence, and (iii) nonidentity between a
  same-depth discrete row and the binary/global-q partial sums, whose summands
  are themselves pointwise equal
completed commits: prior all-real Laplace tranche accepted on main; merge
  checkpoints 6cb9ff8f0, 4b1f51468, and 8fb9d79de synchronize this branch
  through the current coordinator checkpoint
validated (exact command, SHA/state, exit code): read-only ownership and
  duplicate audits only; every advertised Fabius tip was compared with its
  merge base for both claimed paths, and no branch-unique edit was found
not yet validated: no declaration in this claim has been written or
  elaborated; no Lean, Lake, TeX, PDF, Python audit, or cache-mutating process
  has run for this tranche
requested integration or lease: advertise this ordinary nonoverlapping
  two-source lease under the self-service protocol; later request serialized
  focused validation after a source checkpoint is independently reviewed
conflicts / dependencies: the canonical primary, walkthrough, glossary,
  coverage, audit, frontier, root aggregate, README, AGENTS, coordinator, TeX,
  and PDF paths remain untouched and frozen; the EVO token belongs exclusively
  to codex/fabius-exposition-integration for its three frontier pdflatex passes
next bounded step: commit and push this registry-only claim; reread the board
  and every advertised registry/tip; then edit only the two exact Lean sources
  and this registry, without launching validation
```
