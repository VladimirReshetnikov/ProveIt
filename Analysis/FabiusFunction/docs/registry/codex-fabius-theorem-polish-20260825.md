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

## Source checkpoint: exact finite dependence and pairwise limit independence

Source commit `0f7d53e8c28100f6c883798e352919466fbe49ba` implements the
advertised two-file package.  Its source hashes are:

```text
d4d5d565f101a4a33c209877e4cdc2b701217c97  FabiusDiscreteLimitToeplitz.lean
193cd7d36a05059494b4293a8eda4b81f3f91990  FabiusDiscreteLimitIntegration.lean
```

The Toeplitz module proves the depth-one identity at `x = 1 / 3` over an
arbitrary `RCLike` field,
`D₁(q) = q ^ 2 / 2 - q / 3 + 2 / 9`, records its exact real values `2 / 9`
and `7 / 18` at `q = 0` and `q = 1`, and proves those rows unequal.  The
integration module proves that the difference between any two fixed complex
rows, and separately any two fixed real rows, tends to zero at every fixed
real input.  At the common outer truncation index `n = N = 1`, it also proves
that the real zero-shift row differs from the binary partial sum.  By
`qBinomialFabiusGlobalSummand_eq`, `RCLike.ofReal_sum`, and injectivity of the
real embedding, the final theorem strengthens that comparison to every
literal global-q partial sum over every `RCLike` coefficient field and every
series parameter.

Four independent read-only reviews checked the calculation, limit API,
finite-sum convention, imports, public naming, simp attributes, real-embedding
bridge, and current-main/all-tip collision state.  They found no theorem or
signature blocker.  Review did find and correct two documentation defects
before commit: a false claim that the `x = 1 / 3` comparison was globally the
smallest row-versus-sum witness, and ambiguous wording that could confuse a
common outer truncation index with equal internal spline scales.  The final
source says only what the new declarations and existing pointwise summand
identity prove.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: c2aa5a25c82e50149ab8887f95e7c5bcd6fe62eb
HEAD and dirty paths: 2e8a247a8eaa0353fe5143f7b093b4aaab2ca7d3;
  conflict-free merge of current main is committed, both claimed sources are
  clean, and only this registry is dirty for the present report
writing (exact paths): this registry only for the report; the two claimed
  Lean sources remain leased but frozen at source commit 0f7d53e8c
expected declarations or document claims: all eight advertised declarations
  are implemented; the final q-binomial comparison is stronger than the claim
  draft because it quantifies over arbitrary RCLike K and q : K
completed commits: 137c546b9 (exact-path claim), 0f7d53e8c (two-source
  theorem/documentation checkpoint), 2e8a247a8 (conflict-free merge of
  coordinator main c2aa5a25c)
validated (exact command, SHA/state, exit code): git diff --check and git diff
  --cached --check exited 0 before the source commit; forbidden-declaration
  scans found no sorry, admit, axiom, or opaque; every advertised Fabius tip
  was compared with its merge base and none changes either claimed source;
  four independent hostile/source/API reviews found no remaining blocker
not yet validated: 0f7d53e8c has not been elaborated; no Lean, Lake, TeX,
  PDF, Python audit, or cache-mutating process was launched for this tranche
  because the sole EVO token remains assigned to the frontier PDF lane
requested integration or lease: independent coordinator review, followed by
  serialized +FabiusFunction.FabiusDiscreteLimitToeplitz and then
  +FabiusFunction.FabiusDiscreteLimitIntegration at an immutable accepted
  source tree when the EVO token is explicitly assigned; retain both source
  leases until disposition
conflicts / dependencies: current main changed neither claimed source; the
  canonical primary, walkthrough, glossary, PAPER_COVERAGE, AUDIT_FINDINGS,
  README, root aggregate, frontier, TeX, PDF, AGENTS, and coordinator paths
  remain frozen and untouched by this branch
next bounded step: commit and push this registry report, then freeze source
  and poll the board read-only for review/token disposition; do not launch a
  validator and do not push main
```

### Frozen human-readable reciprocity handoff

After the declarations are compiled and integrated, the primary exposition,
Lean walkthrough, glossary, coverage matrix, paper facade documentation, and
root README should state the exact depth-one quadratic and the values `2 / 9`
and `7 / 18`; pairwise difference convergence for fixed shifts and fixed real
input; and the outer-index-one discrete-row/binary/global-q inequalities.  The
wording must say `n = N = 1`, not “matching internal scales”: the discrete row
internally samples degrees `{1, 2}`, whereas the partial sums use scales
`{0, 1}`.  It must also say explicitly that the binary and literal global-q
summands are pointwise equal to each other—the discrete row is the construction
that differs.

The pairwise limit theorems are pointwise in a fixed input and fixed shifts.
They prove no uniformity and no convergence rate.  Claims of an
`O_Q(4 ^ (-n))` rate, eventual exact stabilization at dyadic inputs, dependence
at every nondyadic input or every finite row, or independence of a separate
synchronized construction remain research-frontier obligations.  No canonical
document path is authorized for this branch, so this is a handoff rather than
a prose edit.

## Coordination checkpoint after main `682222de1`

The clean feature tip `b59e9b7b7` was pushed before synchronization.  After a
fresh fetch, both mandatory policy files were reread with `git show`; the merge
preview found no conflict or overlap in either frozen source path or this
registry.  Merge commit `ca787ce1a7a17f8f2051a1206ea77985b0f7bc37`
incorporates `origin/main` `682222de194637f3a5650b7c1ffce349577cb5ae`
without changing the two-file source checkpoint `0f7d53e8c`.

The current board explicitly recognizes the eight-result tranche, freezes
`FabiusDiscreteLimitToeplitz.lean` and
`FabiusDiscreteLimitIntegration.lean` pending coordinator review, and grants
neither an EVO Lean/Lake token nor a `main` push.  This branch therefore makes
no source or canonical-document edit and launches no Lean, Lake, TeX, PDF,
Python audit, or cache-mutating process.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 682222de194637f3a5650b7c1ffce349577cb5ae
HEAD and dirty paths: ca787ce1a7a17f8f2051a1206ea77985b0f7bc37;
  clean immediately after the conflict-free merge, then only this registry is
  dirty for the present coordination report
writing (exact paths): this branch registry only; both claimed Lean source
  paths remain frozen at source commit 0f7d53e8c
expected declarations or document claims: unchanged eight-result package;
  no expansion of the write set
completed commits: 0f7d53e8c (unelaborated two-source theorem checkpoint),
  b59e9b7b7 (pushed source/status checkpoint), ca787ce1a (conflict-free merge
  of coordinator main 682222de1)
validated (exact command, SHA/state, exit code): merge preview and merge were
  conflict-free; mandatory AGENTS.md and coordinator board were reread from
  origin/main 682222de1; prior read-only static and hostile-review evidence
  remains as recorded above
not yet validated: source commit 0f7d53e8c remains wholly unelaborated; no
  Lean/Lake/TeX/PDF/cache-mutating validation has run for this tranche
requested integration or lease: coordinator review, then separately serialized
  +FabiusFunction.FabiusDiscreteLimitToeplitz followed by
  +FabiusFunction.FabiusDiscreteLimitIntegration only after this exact branch
  receives an explicit EVO build token
conflicts / dependencies: no merge conflict; the source paths are board-frozen
  pending review; canonical documentation, coordination, README, root
  aggregate, frontier, TeX, and PDF paths remain untouched
next bounded step: commit and push this registry-only checkpoint to the feature
  branch, then continue read-only polling; do not build and do not push main
```

## Coordinator integration and focused validation

Coordinator checkpoint `c9d20ed14c7572d4f3f1361c7883085eaf5bb0d8`
integrates the two-source theorem unit.  The coordinator cherry-picked source
commit `0f7d53e8c` as `de8707b44`, then the first Toeplitz build exposed three
proof-elaboration defects: both concrete natural-floor evaluations needed
explicit `Nat.floor_eq_iff` witnesses, and the final generic `RCLike`
normalization needed `push_cast` before `ring`.  That failed attempt supplies no
validation evidence.

Repair `8e09c4d98ff1a42fe5d8f1ebf9099a8b0d25d9` changes no public
statement.  At that immutable repaired tree the coordinator ran the two
requested gates separately with `LAKE_JOBS=1`:

```text
lake build +FabiusFunction.FabiusDiscreteLimitToeplitz   # 3320 jobs, exit 0
lake build +FabiusFunction.FabiusDiscreteLimitIntegration # 3422 jobs, exit 0
```

Both completed without warnings.  Feature merge
`f1e1ddf8bf539fbeee68eeebb6e1c5229736d90c` incorporates that validated
mainline result.  Its sole content conflict was the pre-repair Toeplitz proof;
the resolution retains the coordinator repair and is byte-identical to the
validated main blob `d1927c1ae8ff43af1f5dc41541b2cd4df1a4d4cb`.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: c9d20ed14c7572d4f3f1361c7883085eaf5bb0d8
HEAD and dirty paths: f1e1ddf8bf539fbeee68eeebb6e1c5229736d90c;
  clean immediately after the validated-main merge, then only this registry is
  dirty for the present report
writing (exact paths): this branch registry only; both Lean source paths are
  released and no canonical document path is claimed
expected declarations or document claims: all eight advertised declarations
  are integrated on main with unchanged public statements
completed commits: de8707b44 (coordinator source cherry-pick), 8e09c4d98
  (statement-preserving elaboration repair), c9d20ed14 (published coordinator
  disposition), f1e1ddf8b (feature synchronization and exact-blob conflict
  resolution)
validated (exact command, SHA/state, exit code): at immutable coordinator tree
  8e09c4d98, separate LAKE_JOBS=1 builds of
  +FabiusFunction.FabiusDiscreteLimitToeplitz (3320 jobs) and
  +FabiusFunction.FabiusDiscreteLimitIntegration (3422 jobs) both exited 0
  without warnings; resolved Toeplitz blob equals main blob d1927c1ae
not yet validated: the earlier Toeplitz attempt at de8707b44 failed and is not
  evidence; this EVO worktree launched no Lean/Lake/TeX/PDF/Python audit or
  cache-mutating validator
requested integration or lease: source integration is complete and both source
  leases are released; request a separately identified successor owner and
  exact-path grant for the frozen human-readable reciprocity handoff above
conflicts / dependencies: the sole source conflict was resolved wholly inside
  this branch's former claim to the already validated main blob; canonical
  exposition, walkthrough, frontier, glossary, coverage, README, aggregate,
  TeX, and PDF paths remain unclaimed and untouched by this branch
next bounded step: commit and push this registry-only report; await the
  coordinator's exact successor-document or new-source disposition; run no
  validator without an explicit EVO token and never push main
```

## Coordination checkpoint after fetched main `b0b896e39`

At `2026-08-25T20:07:08-07:00`, this branch stopped all expansion and reread
both mandatory policy files directly from fetched `origin/main` with
`git show`.  The exact branch instruction says that the preceding source unit
is integrated and validated, all former source leases are released, this
branch has no EVO build token, and a future ordinary source lane would require
a new registry-first claim.  No such claim is made here.

The local feature checkpoint was clean at
`6c1047eabad48d2860d43250e7745dd30eb02e9e`, which preserves the earlier
conflict-free merge of coordinator checkpoint `f556a126e`.  Fetched main has
since advanced to `b0b896e39a7af565d14d56cbc7cd653db1c3ba68`; it is left
unmerged under this coordination freeze.  No dirty work was stashed, reset,
discarded, overwritten, or merged over.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: b0b896e39a7af565d14d56cbc7cd653db1c3ba68
HEAD and dirty paths: 6c1047eabad48d2860d43250e7745dd30eb02e9e;
  the worktree was clean before this reply, and only this registry file is
  dirty for the present status checkpoint
writing (exact paths):
  docs/registry/codex-fabius-theorem-polish-20260825.md only
expected declarations or document claims: none; the prior eight-result
  discrete-limit unit is integrated and its source leases are released; a
  read-only survey of a possible all-order Laplace-moment reflection identity
  remains unclaimed and has produced no source or human-document edit
completed commits: f1e1ddf8b (feature merge of the repaired, validated
  discrete-limit source), 3102741f2 (published integration disposition), and
  6c1047eab (conflict-free feature merge of coordinator main f556a126e)
validated (exact command, SHA/state, exit code): no new validation was run in
  this worktree; the prior coordinator evidence remains the two separate
  LAKE_JOBS=1 builds at repaired tree 8e09c4d98,
  +FabiusFunction.FabiusDiscreteLimitToeplitz (3320 jobs, exit 0) and
  +FabiusFunction.FabiusDiscreteLimitIntegration (3422 jobs, exit 0), both
  without warnings
not yet validated: local merge 6c1047eab has not been compiled as an
  immutable tree by this worktree; the unclaimed Laplace-reflection proof plan
  has neither been written nor elaborated; no Lean, Lake, LaTeX, PDF, Python
  audit, or cache-mutating validation command was launched at this checkpoint
requested integration or lease: none; no source/document lease and no EVO
  build token are requested by this frozen status reply
conflicts / dependencies: fetched main b0b896e39 is not merged; relative to
  local HEAD it changes four unrelated reviewed Lean modules plus the
  coordinator and theorem-polish registries.  Canonical exposition,
  walkthrough, frontier TeX/PDF, README, coordination files, coverage/audit
  files, and the root Fabius aggregate remain untouched
next bounded step: commit and push this status only to the feature branch,
  never to main and never with force; then remain read-only until the board
  grants an exact source path or physical-host build token
```

### Final pre-push refresh at `99b67cf5b`

The mandatory fetch immediately before publication advanced `origin/main`
from `b0b896e39` to `99b67cf5b5b8084d097205d1f701d13285ecd3b7` by one
coordinator-registry-only commit granting the frontier successor's codexbox
PDF stage.  The exact theorem-polish instruction is unchanged: former source
leases are released, no new claim exists here, and this branch has no EVO
validation token.  The board records EVO as idle and coordinator-reserved.

Registry-only preservation commit `35e9ccef6d2d4a160694d42c836781dab7a82523`
was pushed by fast-forward to the feature branch; it was not amended and no
force was used.  This addendum updates only the fetched-main snapshot.  Local
HEAD `35e9ccef6` was clean before the addendum, no source or document path was
edited, fetched main remains unmerged, and no validation process was launched.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 99b67cf5b5b8084d097205d1f701d13285ecd3b7
HEAD and dirty paths: 35e9ccef6d2d4a160694d42c836781dab7a82523;
  clean after its feature-only fast-forward push, then only this registry is
  dirty for the fetched-main addendum
writing (exact paths): this branch registry only
expected declarations or document claims: none
completed commits: 35e9ccef6 (published coordination-freeze checkpoint)
validated (exact command, SHA/state, exit code): no new validation; no Lean,
  Lake, LaTeX, PDF, Python audit, or cache-mutating command was launched
not yet validated: current local feature tree; the read-only, unclaimed
  Laplace-reflection proof design has not been written or elaborated
requested integration or lease: none; no source/document path or build token
conflicts / dependencies: main's only b0b896e39..99b67cf5b delta is the
  coordinator registry; the assigned codexbox PDF token does not grant an EVO
  validator or any theorem-polish write path
next bounded step: push this addendum to the feature branch without force,
  then remain read-only pending an explicit board assignment
```

## Ordinary claim: all-order reflection of tilted moments

Claim prepared at `2026-08-25T20:15:34-07:00` after a fresh full read of
`AGENTS.md` and the coordinator board from `origin/main` `99b67cf5b`, followed
by the conflict-free merge `44d0ac8827fd086d5512063354d8211880467cca`.
The target source is byte-identical to current main at Git blob
`916b0bb137fccea319245d68e197eaba92349904`; no Lean source has yet been
edited.  This claim converts the previously read-only proof survey into one
exact ordinary path while leaving all canonical document paths serialized.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 99b67cf5b5b8084d097205d1f701d13285ecd3b7
HEAD and dirty paths: 44d0ac8827fd086d5512063354d8211880467cca;
  clean after a conflict-free merge of current main, then only this registry
  is dirty for the exact-path claim
writing (exact paths): this registry initially; after this claim is pushed and
  the required live-tip collision audit remains green, only
  Lean/FabiusFunction/ProbabilityLaplaceMoments.lean and this registry
expected declarations or document claims:
  integral_unit_eq_integral_one_sub_of_reflection, extracting reflection of
    arbitrary continuous observables against the unit-interval restriction
    without a global support or finiteness hypothesis;
  unitLaplaceMoment_reflection, proving for every k and real tilt s the signed
    binomial transform of the complete unit Laplace-moment hierarchy under
    reflection, using only finite-on-compacts for termwise integrability;
  fabiusLaplaceMoment_reflection, transporting that transform to the Fabius
    probability law;
  preserve every existing unit/fabius zero-reflection and centered-even public
    signature, optionally shortening only the Fabius zero proof to the k = 0
    compatibility specialization if elaboration confirms it;
  strengthen the module overview and declaration doc comments, but make no
    canonical TeX/PDF or other human-document edit under this source claim
completed commits: 44d0ac882 (conflict-free merge of origin/main 99b67cf5b);
  no source checkpoint exists yet
validated (exact command, SHA/state, exit code): read-only mathematical and
  Mathlib-source preflight only; the k = 0, 1, and 2 cases independently
  confirm the prefactor, signs, binomial indices, and opposite tilt; target
  source blob equals current main; this is not compiler evidence
not yet validated: all three proposed declarations and any proof refactor;
  no Lean, Lake, LaTeX, PDF, Python audit, or cache-mutating command has run,
  because the EVO token remains idle and coordinator-reserved
requested integration or lease: advertise the single ordinary source path and
  three exact declarations above; request no serialized document path and no
  immediate build token; after an independently reviewed source checkpoint,
  request one serialized EVO build of
  +FabiusFunction.ProbabilityLaplaceMoments
conflicts / dependencies: an earlier all-tip audit at main f556a126e found no
  exact or semantic duplicate and no branch-unique target edit; a new audit at
  current main and every newly advertised tip is running and must remain green
  before the source edit begins.  Canonical exposition, walkthrough, frontier,
  PAPER_COVERAGE, AUDIT_FINDINGS, README, AGENTS, coordinator files, PDFs, and
  the root aggregate remain excluded
next bounded step: commit and push this registry-only claim; fetch and reread
  the board; finish the current-main/all-tip collision and hostile proof
  audits; only then edit the one claimed source file, checkpointing it
  explicitly as not compiled
```

## Source checkpoint: the complete reflected moment hierarchy

Source commit `665b6bceaad5e455384a32a172747242a89268ce` implements the
advertised one-file claim.  The committed
`ProbabilityLaplaceMoments.lean` blob is
`6c5f6b96ac3fd6c5038c4421e2ffc3d34a303989`, with content SHA-256
`E6AE0E4A2F8A3D32367E1743906AE6E7D264FF9126A5952AD361B6C60CC29E9B`.

The source extracts reflection of the unit-interval restriction as a reusable
expectation theorem, proves the signed binomial reflection transform in every
raw-moment degree for measures finite on compact sets, and transports the
identity to the Fabius probability law.  No ambient support or global finite-
measure hypothesis is imposed on the generic all-order theorem.  Every old
zero-reflection and centered-even public signature remains unchanged; the
Fabius zero theorem is now the degree-zero compatibility specialization.

The module guide and all three new declaration comments give human-readable
statements and explain the reflection mechanism.  A later canonical-document
owner should map the all-order formula and its degree-one and degree-two
specializations to the three exact new names.  The normalized first-moment
complement and centered oddness are deliberately not claimed as delivered:
they are high-value downstream consequences requiring separately advertised
Lean declarations before they enter the primary exposition or walkthrough.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 2183cfb113765197042628524690794bdf8d07c4
HEAD and dirty paths: 665b6bceaad5e455384a32a172747242a89268ce;
  the claimed source is clean and only this registry is dirty for the report
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/ProbabilityLaplaceMoments.lean; this status reply writes
  only docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims:
  integral_unit_eq_integral_one_sub_of_reflection,
  unitLaplaceMoment_reflection, and fabiusLaplaceMoment_reflection are all
  implemented with the advertised assumptions and statements; existing zero
  and centered-even theorem signatures are preserved
completed commits: db9e26b66 (pushed exact-path/declaration claim) and
  665b6bcea (one-file source, proof, and module-documentation checkpoint)
validated (exact command, SHA/state, exit code): no compiler validation is
  claimed; git diff --check exited 0, the source contains no sorry, admit,
  axiom, or opaque, every new declaration has a doc comment, and three
  independent read-only reviews checked current Mathlib signatures, the
  restrict_map orientation, interval preimage, local-finiteness instance,
  binomial signs and indices, exponential factorization, finite-sum
  integrability, Fabius transport, k = 0 simplification, public API, prose,
  and every advertised branch tip without finding a blocker
not yet validated: commit 665b6bcea has not been elaborated; no Lean, Lake,
  LaTeX, PDF, Python audit, or cache-mutating process was launched.  The live
  20:16 board assigns EVO exclusively to codex/fabius-shifted-prefix-grid
requested integration or lease: independent coordinator source review,
  followed only after an explicit later EVO assignment by one serialized
  LAKE_JOBS=1 build of +FabiusFunction.ProbabilityLaplaceMoments; request no
  document, aggregate, or other serialized-path lease
conflicts / dependencies: while the source was dirty, origin/main advanced to
  2183cfb11 and the shifted-prefix tip to 4367a7f86; both retain target blob
  916b0bb13, have no branch-relative target edit, and claim none of the three
  names.  No merge was attempted over dirty work.  All canonical TeX/PDF,
  README, coverage/audit, coordination, walkthrough, and root aggregate paths
  remain untouched
next bounded step: commit and push this registry report with source checkpoint
  665b6bcea to the feature branch; keep the source frozen and request review
  and a future EVO token.  Do not merge current main until the checkpoint is
  clean and remotely preserved, and do not launch validation unassigned
```

### Clean synchronization through main `de3033392`

The source and report were first preserved remotely at feature tip
`b542c2619`.  After a fresh board read, merge preview showed no overlap with
the claimed source or this registry.  Merge commit
`6a5d98bd0fbabb9e8bca056cf95b8fd560e09383` incorporates fetched main
`de303339202ef0b7fb99da83003d4b841eef9b80` without conflict.  Main changed
only `PeriodicSmooth.lean`, the canonical frontier TeX/PDF pair, the frontier
successor registry, and the coordinator board; the reflected-moment source
blob remains exactly `6c5f6b96ac3fd6c5038c4421e2ffc3d34a303989`.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: de303339202ef0b7fb99da83003d4b841eef9b80
HEAD and dirty paths: 6a5d98bd0fbabb9e8bca056cf95b8fd560e09383;
  clean after the conflict-free merge, then only this registry is dirty for
  the synchronization report
writing (exact paths): this registry only; source commit 665b6bcea remains
  frozen in Lean/FabiusFunction/ProbabilityLaplaceMoments.lean
expected declarations or document claims: unchanged implemented set of
  integral_unit_eq_integral_one_sub_of_reflection,
  unitLaplaceMoment_reflection, and fabiusLaplaceMoment_reflection
completed commits: 665b6bcea (uncompiled one-source theorem checkpoint),
  b542c2619 (pushed source report), and 6a5d98bd0 (conflict-free merge of main
  de3033392)
validated (exact command, SHA/state, exit code): source-review evidence is
  unchanged; merge preview and merge were conflict-free, post-merge
  git diff --check exited 0, and the source blob is byte-identical to the
  three-review checkpoint
not yet validated: neither source commit 665b6bcea nor merged feature tree
  6a5d98bd0 has been elaborated; no Lean, Lake, LaTeX, PDF, Python audit, or
  cache-mutating process was launched by this worktree
requested integration or lease: independent review and a later explicit EVO
  assignment for one LAKE_JOBS=1
  +FabiusFunction.ProbabilityLaplaceMoments build; no document lease
conflicts / dependencies: none; the feature's net delta from main is exactly
  the claimed ProbabilityLaplaceMoments source plus this branch registry.
  EVO remains assigned to the shifted-prefix branch on the fetched board
next bounded step: commit and push this post-merge registry checkpoint, notify
  the coordinator of the exact immutable source commit/blob, and keep the
  source frozen until review and token disposition
```

## Coordinator acceptance and repaired synchronization through main `1401f2d9b`

The 20:44 PDT board accepts the reflected-moment tranche.  The coordinator
integrated source commit `665b6bcea` as `c80f61c90`.  The first focused build
then exposed one proof-elaboration defect: bare `simp [neg_pow]` recursively
reconsidered the `(-1)^j` factor it had generated.  That failed invocation
supplies no validation evidence.  Repair `6b6757e90` replaces the recursive
simplification with one explicitly typed `neg_pow` identity; it changes no
theorem statement, formula, import, or public API.

At the repaired immutable tree, the coordinator's serialized command
`LAKE_JOBS=1 lake build +FabiusFunction.ProbabilityLaplaceMoments` completed
3187 jobs in 18 seconds, exited 0, and reported no warnings.  The accepted
source blob is `488d9fd4c9acfa5100df0dcf04b7f81af967973f`.

After fetching and rereading the new board, merge preview found exactly one
conflict: the original uncompiled `simp only [neg_pow, one_pow, mul_one]` line
versus the coordinator's accepted explicit identity in the formerly claimed
source.  Merge `a803a38ea` retains the coordinator repair.  The resulting
worktree source blob is byte-identical to the accepted mainline blob above.
No other claimed, serialized, document, registry, or generated path
conflicted.

Three final read-only reconnaissance lanes identified useful later work but
made no claim and changed no file.  First, a measurable-equivalence proof can
remove the continuity hypothesis on the generic reflection integrand entirely;
a sharper base theorem can also use only finiteness and reflection of the
unit-interval restriction.  Second, a separately advertised
`NegativeLaplaceDerivatives.lean` tranche could prove
`normalizedLaplaceMoment_reflection`,
`normalizedLaplaceMoment_one_complement`, and
`normalizedLaplaceMoment_one_sub_half_odd`.  Third, exact insertion points and
Lean-name cross-references are mapped for the primary exposition, Lean
walkthrough, and frontier companion.  Those canonical documents remain frozen,
and none of these uncompiled follow-ons is presented as delivered.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 1401f2d9b6cfd02e0b6a72ee60869b6df0bb776c
HEAD and dirty paths: a803a38ea after the repaired-main merge; clean before
  this status update, then only this branch registry is dirty
writing (exact paths): this status reply writes only
  docs/registry/codex-fabius-theorem-polish-20260825.md; the merge conflict in
  Lean/FabiusFunction/ProbabilityLaplaceMoments.lean was resolved to the exact
  accepted mainline blob and does not expand the source write set
expected declarations or document claims: the accepted public set remains
  integral_unit_eq_integral_one_sub_of_reflection,
  unitLaplaceMoment_reflection, and fabiusLaplaceMoment_reflection; existing
  zero-reflection and centered-even signatures remain compatibility results
completed commits: 665b6bcea (original source checkpoint), c704f1ae9 (last
  remotely preserved feature status), c80f61c90 (coordinator integration),
  6b6757e90 (statement-preserving coordinator repair), and a803a38ea
  (feature merge of accepted main and exact repair resolution)
validated (exact command, SHA/state, exit code): at coordinator repair
  6b6757e90, LAKE_JOBS=1 lake build
  +FabiusFunction.ProbabilityLaplaceMoments completed 3187 jobs in 18 seconds,
  exit 0, no warnings; the merged feature source has the identical Git blob
  488d9fd4c9acfa5100df0dcf04b7f81af967973f; merge-side git diff --check
  exited 0
not yet validated: this EVO worktree launched no Lean, Lake, LaTeX, PDF,
  Python audit, or cache-mutating process; the three read-only follow-on ideas
  above are source-designed only and have not been advertised or compiled
requested integration or lease: none; the source is integrated, repaired,
  compiled, and released.  This branch has no Lean/Lake, document, aggregate,
  or serialized-path token
conflicts / dependencies: the sole merge conflict was confined to the prior
  claimed source and resolved to the coordinator-validated bytes.  All
  canonical TeX/PDF, README, coverage/audit, coordination, walkthrough, and
  root aggregate paths remain unedited by this branch
next bounded step: commit and push this registry-only status to the feature
  branch, then stop source/document expansion and launch no build until a later
  exact board assignment
```

## Claim: normalized reflection and tilted-variance parity

This is a new ordinary one-source claim, separate from the integrated raw
reflection tranche.  It claims exactly:

- `Lean/FabiusFunction/ProbabilityLaplaceMoments.lean`; and
- this branch registry.

The source change will replace that module's direct `LaplaceMoments` import
with `NegativeLaplaceDerivatives`, retaining its other imports.  Static import-
closure inspection shows the direction is acyclic and costs the probability
module exactly one internal dependency.  The reverse direction would make all
fifty transitive users of `NegativeLaplaceDerivatives` inherit the probability
representation and existence layers, so it is deliberately avoided.

The exact proposed public declarations are:

1. `normalizedLaplaceMoment_reflection` — reflection at the opposite tilt
   descends to every normalized moment as the signed binomial transform;
2. `normalizedLaplaceMoment_one_complement` — normalized means under opposite
   exponential tilts sum to one;
3. `normalizedLaplaceMoment_one_sub_half_odd` — centering the normalized tilted
   mean at `1 / 2` gives an odd function; and
4. `negativeLaplaceLogSecond_even` — the normalized tilted variance is an even
   function of the tilt on the whole real line.

The fourth result is the strongest bounded degree-two consequence: reflection
transports one tilted law to the opposite tilt without changing its variance.
Equivalent first-cumulant wrappers and third/fourth-cumulant parity are omitted
to keep this API and its future documentation surface focused.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 39ad356c7a433c1b7dfdaec5bb3e3e4163c9fd35
HEAD and dirty paths: e0644592affc0fdb798890c16b6c0a1432dec018;
  clean after merging current main, then only this registry is dirty for the
  exact-path/declaration claim
writing (exact paths): after this claim is committed and pushed, only
  Lean/FabiusFunction/ProbabilityLaplaceMoments.lean; this claim edits only
  docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims:
  normalizedLaplaceMoment_reflection,
  normalizedLaplaceMoment_one_complement,
  normalizedLaplaceMoment_one_sub_half_odd, and
  negativeLaplaceLogSecond_even; no document claim
completed commits: 3bf399e63 (accepted reflected-moment status) and
  e0644592a (conflict-free merge of current main 39ad356c7); no source commit
  exists for this new claim
validated (exact command, SHA/state, exit code): read-only architecture,
  Mathlib-signature, proof-algebra, and all-tip collision preflight only; all
  three reviews are green.  The current target blob is
  488d9fd4c9acfa5100df0dcf04b7f81af967973f on main and has no unique edit on
  any of 16 audited Fabius/Claude tips
not yet validated: all four declarations and the import change are unedited
  and uncompiled; no Lean, Lake, LaTeX, PDF, Python audit, or cache-mutating
  command has run.  Both host tokens are idle but unassigned, which is not a
  grant
requested integration or lease: advertise this single ordinary source path;
  after a reviewed immutable source checkpoint, request one serialized EVO
  `LAKE_JOBS=1 lake build +FabiusFunction.ProbabilityLaplaceMoments`; request
  no document, aggregate, facade, or other serialized-path lease now
conflicts / dependencies: all 16 fetched Fabius/Claude tips retain their own
  merge-base target blob or lack the path; all active claims are disjoint.
  No exact name or semantic duplicate exists.  The prior raw-reflection lease
  on this path is integrated, validated, and explicitly released
next bounded step: commit and push this registry-only claim; fetch and reread
  the board and every advertised tip; only if the collision audit remains
  green, implement the four results in the one claimed source without running
  unassigned validation
```

## Source checkpoint: normalized reciprocity and variance parity

Source commit `493575690f17c8c7d85e8b1b61edaf321d581a68` implements the
complete four-name claim.  The committed `ProbabilityLaplaceMoments.lean` blob
is `8a1d896e324a45f2681259f2c83e50fdfb78e238`, with content SHA-256
`6A684C17CBC0965DEE6EC2B19EAC577F36D3F0A8D4B12020C56BDCB0EF0FD260`.

The proof cancels the common nonzero exponential factor in the raw numerator
and zeroth-moment denominator, distributes the remaining quotient over the
finite binomial sum, and closes each summand by associativity alone.  The
degree-one specialization gives complementary tilted means and centered
oddness.  Combining degrees one and two with the definition of
`negativeLaplaceLogSecond` proves that the tilted variance is globally even.

The import is intentionally directed from the probability bridge to
`NegativeLaplaceDerivatives`.  This exposes the normalized-moment definitions
where the reflection consequence belongs while keeping the larger analytic
consumer graph free of the probability/existence dependency stack.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: a3cbe179443df1593b50a8034ce456729a004f9d
HEAD and dirty paths: 493575690f17c8c7d85e8b1b61edaf321d581a68;
  claimed source is clean and only this registry is dirty for the report
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/ProbabilityLaplaceMoments.lean; this status reply writes
  only docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims:
  normalizedLaplaceMoment_reflection,
  normalizedLaplaceMoment_one_complement,
  normalizedLaplaceMoment_one_sub_half_odd, and
  negativeLaplaceLogSecond_even are implemented exactly as advertised; no
  canonical document claim
completed commits: 4267605f0 (pushed exact-path/four-name claim),
  daea529e0 (conflict-free merge of current main a3cbe1794), and
  493575690 (one-source implementation checkpoint)
validated (exact command, SHA/state, exit code): no compiler validation is
  claimed.  git diff --check exited 0; the source adds exactly four documented
  declarations and no other declaration, attribute, instance, alias, sorry,
  admit, axiom, or opaque.  Three independent read-only hostile reviews accept
  the exact Mathlib rewrite orientations, k = 1 and k = 2 reductions,
  Function.Odd/Even directions, variance algebra, import closure, API boundary,
  prose, exact dirty scope, and all 16 fetched Fabius/Claude tips
not yet validated: source commit 493575690 has not been elaborated.  No Lean,
  Lake, LaTeX, PDF, Python audit, or cache-mutating process was launched.  The
  live board leaves EVO idle but unassigned
requested integration or lease: assign the sole EVO Lean/Lake token for one
  serialized `LAKE_JOBS=1 lake build
  +FabiusFunction.ProbabilityLaplaceMoments` at this immutable source; request
  no document, aggregate, facade, or other source lease
conflicts / dependencies: none.  The source preimage equals current-main blob
  488d9fd4c9acfa5100df0dcf04b7f81af967973f; all audited tips retain their own
  merge-base target blob or lack the file.  Active both-papers/effective-bounds
  source claims are disjoint
next bounded step: commit and push this registry report with source checkpoint
  493575690, notify the coordinator, freeze the source, and run no build until
  an explicit exact-tree EVO assignment appears on the board
```

## Accepted checkpoint: normalized reflection hierarchy

The coordinator integrated source commit `493575690f17c8c7d85e8b1b61edaf321d581a68`
as mainline commit `853a09a80`.  On the assigned codexbox build host, the exact
serialized command

```text
LAKE_JOBS=1 lake build +FabiusFunction.ProbabilityLaplaceMoments
```

completed all 3188 jobs with exit code 0.  The build emitted one nonblocking
`unnecessarySimpa` linter suggestion in the new normalized-reflection proof;
that style-only cleanup is not claimed here and would require a fresh exact
source claim before any edit.  The coordinator has released both the source
lease and the build token.

Feature merge `74ff5586db124f542ffa1c70eea09d2801fc8259` incorporates
`origin/main` at `ff675711f02a84c365cf4824c257ad593933e46d`.  The merged
`ProbabilityLaplaceMoments.lean` remains byte-identical to the compiled source,
with Git blob `8a1d896e324a45f2681259f2c83e50fdfb78e238` and content SHA-256
`6A684C17CBC0965DEE6EC2B19EAC577F36D3F0A8D4B12020C56BDCB0EF0FD260`.

A strict read-only reciprocity audit found that the mathematics is coherent
but the theorem-to-exposition correspondence is not yet complete.  Only
`fabiusLaplaceMoment_zero_reflection` and
`fabiusLaplaceMoment_zero_centered_even` currently have both their exact
formulas and exact Lean-name cross-references in the canonical exposition.
The generic integral and unit-moment reflection lemmas, the all-order Fabius
raw transform, and all four normalized consequences still need exact prose
statements and name references.  Existing probability-law reflection prose
also needs the exact names `uniformProduct_map_reflectCoordinates`,
`weightedCoordinateSum_reflect`, `weightedSumDistribution_reflection`, and
`weightedSumCDF_symmetry` attached to it.

The audit additionally identified two genuine correspondence hazards for a
future document owner.  The frontier's complex identity
`A(z) = exp(z) A(-z)` has no exact public complex Lean theorem; the real
zeroth-moment theorem is not a substitute.  The walkthrough's unconditional
derivative interpretation of the first normalized moment exceeds the current
positive-scale hypothesis of `negativeLaplaceLog_hasDerivAt`; its all-real
content must presently be phrased as the algebraic identity defining
`negativeLaplaceLogFirst`.  Future prose should use a distinct normalized
notation such as `R_k = M_k / M_0`, retain the alternating signs in the raw and
normalized transforms, and state that `R_2 - R_1^2` is even rather than
incorrectly claiming that `R_2` itself is even.

No canonical document path is claimed.  The exact insertion map is ready for
the primary exposition's reflection and formal-proof paragraphs, the Lean
walkthrough's probability/reflection and logarithmic-derivative sections, and
the frontier companion's reflection and module-ledger sections, but all such
paths remain frozen until the board grants a document lease.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: ff675711f02a84c365cf4824c257ad593933e46d
HEAD and dirty paths: 74ff5586db124f542ffa1c70eea09d2801fc8259;
  clean after the conflict-free main merge, then only this branch registry is
  dirty for the acceptance report
writing (exact paths): this status reply writes only
  docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims: the accepted public source set is
  normalizedLaplaceMoment_reflection,
  normalizedLaplaceMoment_one_complement,
  normalizedLaplaceMoment_one_sub_half_odd, and
  negativeLaplaceLogSecond_even; no canonical document claim
completed commits: 493575690 (feature source), 853a09a80 (coordinator
  integration), and 74ff5586d (feature merge through main ff675711f)
validated (exact command, SHA/state, exit code): coordinator build at the
  integrated source, LAKE_JOBS=1 lake build
  +FabiusFunction.ProbabilityLaplaceMoments, 3188 jobs, exit 0, with one
  nonblocking unnecessarySimpa linter; merged feature source has identical Git
  blob 8a1d896e324a45f2681259f2c83e50fdfb78e238
not yet validated: this EVO worktree ran no Lean, Lake, LaTeX, PDF, Python
  audit, or cache-mutating process; canonical document reciprocity remains
  incomplete and no future theorem sketch is represented as compiled
requested integration or lease: none; source and build leases are released,
  and no document, aggregate, facade, coordination, or further source lease is
  held
conflicts / dependencies: none in the ff675711f merge.  Canonical TeX/PDF,
  README, coverage/audit, coordination, walkthrough, and root aggregate paths
  remain unedited.  A future document pass must not identify the complex
  reflection claim with its real-axis restriction or overstate the domain of
  the logarithmic derivative theorem
next bounded step: commit and push this registry-only acceptance checkpoint to
  the feature branch, then freeze the write set and await a fresh exact board
  assignment before any source, document, or build action
```

## Pre-push main synchronization

After the acceptance report was committed as `bdee8a653`, a fresh fetch moved
`origin/main` to `df3e05c48bd7a4678c6118ba2e26b7d1ec2a6bf2`.  The live
board still records the normalized-reflection tranche as integrated and green,
with every lease released.  Clean feature merge
`bb1a305b9ec41632f552143befa76b752b90a42a` incorporates that mainline
checkpoint without conflict.  Its incoming signed dyadic-prefix Lean paths are
disjoint from this completed tranche, and the normalized-reflection source
blob remains exactly `8a1d896e324a45f2681259f2c83e50fdfb78e238`.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: df3e05c48bd7a4678c6118ba2e26b7d1ec2a6bf2
HEAD and dirty paths: bb1a305b9ec41632f552143befa76b752b90a42a;
  clean after the main merge, then only this branch registry is dirty for this
  synchronization record
writing (exact paths): only
  docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims: no new declaration or document
  claim; normalized-reflection acceptance remains unchanged
completed commits: bdee8a653 (acceptance evidence) and bb1a305b9 (merge of
  current main df3e05c48)
validated (exact command, SHA/state, exit code): no new compiler invocation;
  origin/main is an ancestor of the merge tip, and the normalized-reflection
  source retains the exact coordinator-compiled Git blob
not yet validated: no local Lean/Lake/LaTeX/PDF process ran; no future source
  design or document handoff is represented as implemented or compiled
requested integration or lease: none; all source, build, document, facade, and
  aggregate leases remain released
conflicts / dependencies: merge completed without conflict; incoming ordinary
  Lean changes are disjoint, and all serialized canonical paths remain frozen
next bounded step: commit and push this registry-only sync to the feature
  branch, then await a fresh exact board assignment
```

## Claim: exact compact Lambert-W obstruction

The exact source supplied by the user is the 13 January 2022 comment on
<https://math.stackexchange.com/questions/4354350/extracting-an-asymptotic-from-a-sequence-defined-by-a-recurrence-relation>.
Here `~` explicitly means that the ratio tends to one as `x` tends to zero
from the right.  The displayed nonperiodic constant, prefactor, lower branch,
and Lambert polynomial are correct, but the claimed equivalence is false: the
answer immediately above first derives a tiny nonconstant periodic term and
then says it will be ignored.  Its small amplitude does not make it tend to
zero.

This ordinary source claim is exactly:

- `Lean/FabiusFunction/FabiusWikipediaMain.lean`;
- `Lean/FabiusFunction/FabiusSharpAsymptotic.lean`; and
- this branch registry.

The proposed public surface is exactly:

1. `fabiusWikipediaLambertMain` -- the logarithm of the precise compact
   uncorrected expression in the user's screenshot;
2. `fabiusCorrectedWikipediaMain_eq_WikipediaLambertMain_add` -- the exact
   decomposition of the already-proved corrected main as the online main plus
   `negativeLaplacePsi (fabiusLambertPhase x)`;
3. `isEquivalent_exp_iff_tendsto_log_sub` -- for an eventually positive
   function, the reusable equivalence between a ratio-one exponential
   asymptotic and a vanishing logarithmic error;
4. `log_fabius_sub_WikipediaLambertMain_not_tendsto_zero` -- the omitted
   periodic logarithmic residual does not vanish;
5. `log_fabius_sub_WikipediaLambertMain_not_isBigO` -- in particular the
   exact compact online residual is not `O(1 / (-log x))`; and
6. `fabius_not_isEquivalent_exp_WikipediaLambertMain` -- the exact
   exponentiated expression in the screenshot is not an asymptotic equivalent
   of the Fabius function.

The existing theorem `fabius_isEquivalent_exp_correctedWikipediaMain` already
proves the corrected compact expression.  No saddle estimate or constant is
being reproved.  The new proof will expose the online main verbatim, reuse the
existing exact corrected equivalence and phase-sampling obstruction, and
factor the repeated log/ratio conversion through the new generic iff.  The
body of `fabius_not_isEquivalent_exp_WikipediaElementaryMain` may be shortened
through that iff, but its declaration, hypotheses, conclusion, and attributes
will remain unchanged.

Static Fourier comparison also identifies the answer's discarded term
exactly: with `chi_k = 2*pi*i*k/log 2`, the identity
`Gamma(1-chi_k) = -chi_k*Gamma(-chi_k)` turns its coefficient into the proved
Fourier coefficient of `negativeLaplacePsi`.  At the endpoint saddle its
argument is the exact phase `-W_{-1}(-x*log 2)/log 2`.  Thus the corrected
ratio-one expression multiplies the screenshot's right-hand side by the
exponential of that periodic value; no arbitrary constant multiplier repairs
the omitted oscillation.

No document path is claimed here.  The 21:59 PDT live board now records the
user-directed release of the former documentation owner: every canonical
document remains frozen, and no TeX/PDF lane is assigned.  It conditionally
reserves only the primary TeX/PDF pair for this branch after the exact
two-source Lean checkpoint is implemented, independently reviewed, and
accepted.  Until a later board checkpoint activates that lease, coverage,
primary, walkthrough, frontier, and every matching PDF remain untouched.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 29791005881f1563eba9618e6d75b9db50b045a2
HEAD and dirty paths: ea42818d6856d88c73ddb041e55a9325b5d4d1c8;
  only this branch registry is dirty for the exact two-source/six-name claim;
  fetched main advanced after the prior clean merge and will be merged only
  after this preservation checkpoint is committed and pushed
writing (exact paths): after this claim is committed and pushed, only
  Lean/FabiusFunction/FabiusWikipediaMain.lean and
  Lean/FabiusFunction/FabiusSharpAsymptotic.lean; this claim writes only
  docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims: the six exact public declarations
  listed above; no canonical document claim until the board activates its
  conditional primary reservation
completed commits: ea42818d6 (conflict-free merge of current main 0bc0bf551);
  no source commit exists for this claim
validated (exact command, SHA/state, exit code): strict read-only mathematical,
  source/API, online-source, Fourier-normalization, proof-architecture, and
  all-tip name/path collision audits only.  The target current-main blobs are
  1bbc728a8d3d4c44c58659b0913805e925c4e116 and
  15b1132214ba9d804abd919b465d7d5346f8d42e; no fetched active tip carries a
  competing name or current unique edit to either released source path
not yet validated: the six declarations are unedited and uncompiled; no local
  Lean, Lake, LaTeX, PDF, Python audit, or cache-mutating process has run
requested integration or lease: advertise this ordinary two-source claim.
  After an immutable reviewed checkpoint, request one serialized EVO
  `LAKE_JOBS=1 lake build +FabiusFunction.FabiusSharpAsymptotic`.  Separately,
  await activation of the board's conditional primary TeX/PDF reservation;
  request no other document, facade, root, aggregate, or build lane now
conflicts / dependencies: the former generalizations claim touching
  FabiusSharpAsymptotic.lean is integrated and explicitly released.  Historical
  Claude tips are older blobs, not active unique claims.  Current effective-
  bounds and both-papers paths are disjoint.  The former document-owner lease
  is released, but every canonical document remains frozen until an explicit
  board grant
next bounded step: commit and push this registry-only claim; fetch and reread
  the board plus every advertised tip; if the two ordinary source paths remain
  collision-free, implement the exact online-main bridge without launching an
  unassigned build
```

## Source checkpoint: exact compact Lambert-W obstruction

Source commit `b0600193b8f33bea28cec01a07bca2688a175441` implements exactly the
advertised two-path/six-declaration tranche.  It preserves the established
corrected main definition and adds a separate totalized definition for the
logarithm of the compact nonperiodic online expression, with its positive
lower-branch interpretation stated explicitly in the doc comment.  The exact
decomposition into that main plus `negativeLaplacePsi` is definitional.

The final module now factors the shared analytic argument through
`isEquivalent_exp_iff_tendsto_log_sub`.  Subtracting the already-proved
corrected logarithmic limit exposes precisely the sampled periodic correction;
its existing phase-sampling theorem therefore gives the new nonconvergence,
sharp-rate failure, and direct ratio-one non-equivalence results without a new
saddle estimate.  The old elementary-expansion theorem is unchanged.

Two independent strict read-only preflights accept the exact diff: the
constant signs, lower branch, positive-side filter, totalization caveat,
declaration order, imports, Mathlib APIs, and subtraction/congruence proof
shape are all consistent with already-used code in the same module.  This is
source-level evidence only.  No Lean/Lake token is assigned, so the checkpoint
is deliberately and explicitly uncompiled.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: c5ee98fc72489312e042eb0a4f2280827ee96457
HEAD and dirty paths: b0600193b8f33bea28cec01a07bca2688a175441;
  source checkpoint clean, then only this own registry is dirty for the
  immutable handoff report
writing (exact paths): frozen after source checkpoint; the implemented paths
  are Lean/FabiusFunction/FabiusWikipediaMain.lean and
  Lean/FabiusFunction/FabiusSharpAsymptotic.lean; this report writes only
  docs/registry/codex-fabius-theorem-polish-20260825.md
expected declarations or document claims: all six advertised declarations are
  implemented; no canonical document claim is active
completed commits: b0600193b (exact two-source implementation); c673f4f16
  (conflict-free merge of the then-current main); 8c6456646 (registry-first
  claim)
validated (exact command, SHA/state, exit code): at b0600193b, `git diff
  --check` exited 0 before commit; targeted forbidden-declaration scan found no
  sorry/admit/axiom/opaque; two independent strict read-only actual-diff
  preflights found no mathematical, branch, domain, filter, API, import,
  declaration-order, or likely elaboration blocker.  Source blobs are
  61ae4480ff0e8548cc6b9a8b400e845860bae113 and
  e6939d6e8ed76a71c635ef67118c73867ebe2800
not yet validated: no Lean/Lake process has compiled b0600193b; no current
  `.olean`, focused target, facade, aggregate, or remote CI claim is made.  No
  LaTeX/PDF process ran
requested integration or lease: request independent source review, then one
  serialized EVO `LAKE_JOBS=1 lake build
  +FabiusFunction.FabiusSharpAsymptotic`; after source acceptance and green
  validation, activate only the already-conditional primary TeX/PDF reservation
conflicts / dependencies: refreshed audit of all advertised Fabius/Claude tips
  and registries was green.  No active path overlap or candidate-name duplicate
  exists.  The historical FabiusSharpAsymptotic lease is integrated/released.
  Every canonical document remains frozen
next bounded step: commit and push this registry handoff to the feature branch,
  then stop source writes for independent review and an explicit build-token
  decision
```

## EVO validation attempt: shared-cache read failure

The coordinator accepted the frozen two-source handoff for validation and
assigned this exact branch the sole EVO Lean/Lake token for one invocation of
`+FabiusFunction.FabiusSharpAsymptotic`.  Clean merge
`2a0487fc9b65e23a9b86666197d18d9bd296438d` incorporates fetched main
`d33c4f44b3d08f14b15c1514d687a32898569475`.  Immediately before the build,
the two reviewed source blobs remained byte-identical to the handoff:
`61ae4480ff0e8548cc6b9a8b400e845860bae113` and
`e6939d6e8ed76a71c635ef67118c73867ebe2800`; no other Lean or Lake process was
running on EVO.

The single authorized invocation exited `1`.  It did not expose a theorem or
proof elaboration error and never reached the requested final module.  Two
unrelated dependencies failed at their first source position because files in
the shared Mathlib build cache could not be read:

- `FabiusFunction.FabiusLogMainDefect` could not read
  `Mathlib/GroupTheory/OrderOfElement.olean.private`;
- `FabiusFunction.StepMeasureBridge` could not read
  `Mathlib/Analysis/Normed/Module/Alternating/Basic.olean`.

The invocation reached the final `3891`-job graph with last successful progress
`[3889/3891]`, then reported exactly those two failed required targets and
`error: build failed`.  It also replayed the inherited nonblocking
`unnecessarySimpa` linter at `ProbabilityLaplaceMoments.lean:652`.  Per the
board's failure instruction, no retry, second target, document process, cache
repair, or other validation command was launched.  This record releases the
EVO token and makes no compiler-validation claim for the six new declarations.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: d33c4f44b3d08f14b15c1514d687a32898569475
HEAD and dirty paths: 2a0487fc9b65e23a9b86666197d18d9bd296438d;
  clean after the conflict-free main merge, then only this own registry is
  dirty for the failed-build report
writing (exact paths): this status reply writes only
  docs/registry/codex-fabius-theorem-polish-20260825.md; both accepted Lean
  sources remain frozen and byte-identical; no document path is active
expected declarations or document claims: the same six implemented compact
  Lambert-W declarations; no new declaration or document claim
completed commits: b0600193b (exact two-source implementation), 20751d800
  (immutable handoff), and 2a0487fc9 (conflict-free merge of current main)
validated (exact command, SHA/state, exit code): at merged HEAD 2a0487fc9 with
  exact source blobs 61ae4480f and e6939d6e8, the sole authorized command
  `$env:LAKE_JOBS='1'; lake build
  +FabiusFunction.FabiusSharpAsymptotic` exited 1 after two shared-Mathlib-cache
  read failures; no source elaboration failure was reported
not yet validated: FabiusFunction.FabiusSharpAsymptotic was not built, so none
  of the six new declarations has compiler evidence on this merged tree; no
  LaTeX/PDF process ran
requested integration or lease: report the cache failure and release the EVO
  token; await coordinator disposition before any cache repair, retry, source
  edit, integration, or activation of the conditional primary-document lease
conflicts / dependencies: merge was conflict-free and the accepted source
  blobs remained exact.  Validation is blocked only by unreadable shared
  Mathlib artifacts in two unrelated dependency modules.  Every canonical
  document remains frozen
next bounded step: commit and push this registry-only failure checkpoint to
  the feature branch, notify the coordinator, and remain read-only pending a
  fresh board instruction
```

## Accepted Lean gate and primary-exposition handoff

The coordinator integrated the exact frozen source as
`8d928a55ff19a856e1d7a9083e5e102fff857804`.  At that immutable tree the sole
serialized command

```text
LAKE_JOBS=1 lake build +FabiusFunction.FabiusSharpAsymptotic
```

completed all 3891 jobs and exited `0`; its only diagnostic was the inherited
nonblocking `unnecessarySimpa` linter in
`ProbabilityLaplaceMoments.lean`.  This exact-tree coordinator evidence
supersedes the preceding EVO cache-failure attempt without erasing that honest
machine-specific record.  Both Lean source leases and both host Lean/Lake
tokens are released.

Under the subsequently activated primary-document lease, commit
`2546fe21b` updates exactly the canonical TeX/PDF pair.  It adds one
formalization-backed subsection that prints the January 2022 compact
lower-Lambert expression, explains the multiplier-one failure, prints the
corrected expression with the essential `+ negativeLaplacePsi` term at phase
`-W / log 2`, and gives human-readable counterparts for all six accepted
declarations.  It explicitly says that this tranche does not by itself rule
out every arbitrary constant multiplier; no liminf, limsup, cluster-set, or
numerical-extremum claim was added.  The module map now includes
`FabiusWikipediaMain.lean`, the source provenance is exact, and the document
snapshot is the validated source commit `8d928a55f`.

The document was built under the sole EVO TeX/PDF stream with sidecar job name
`Fabius_Function_and_Rvachev_Up_codex_lambert`.  Three sequential invocations
of

```text
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error
  -jobname=Fabius_Function_and_Rvachev_Up_codex_lambert
  Fabius_Function_and_Rvachev_Up.tex
```

all exited `0`, producing 57, 59, and 59 pages.  The third pass was settled:
no undefined reference or citation, rerun request, changed label, duplicate
label, fatal/LaTeX error, overfull box, or rendered `??` occurred.  Its sole
underfull diagnostic is the unchanged `Analyticity, inverse, elementary
obstruction` module-map cell.  `pdfinfo` reports 59 A4 pages; `pdffonts`
reports every font embedded.  Text extraction found no placeholder, and
raster inspection covered every changed page: title/contents pages 1--3 and
pages 50--59 containing the insertion and all shifted downstream material.

The final artifacts are:

- TeX Git blob `5071d1f32f5f732e7cc59f569190532b6d815d57`, SHA-256
  `D36680516B8F73CAE3B4237477A8B04803A5ED5EBDFA741A86CA6BE7CEA4C2DD`;
- PDF Git blob `4529d9c453d647e4068e2ff5527c417f5564f5d0`, SHA-256
  `FA8DAF5CB82DEFB7E807A09EF6FBA43C48C4E312862ACAFC7BDE36340EC36C51`,
  1,018,335 bytes.

The matching settled PDF was installed only after those gates.  Generated
sidecar auxiliaries were moved out of the repository, so no `.aux`, `.log`,
`.out`, `.toc`, or staging PDF remains in the worktree.  This handoff
explicitly releases the primary-document lease and EVO TeX/PDF stream.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-theorem-polish-20260825 /
  C:/Users/vresh/.codex/worktrees/10ef/ProveIt / EVO (Windows)
fetched main SHA: 5b053a32b10e758e39f1be23cb2e8d821fba8de6
HEAD and dirty paths: 2546fe21b395a469dd0cc3c36c62993cf04f93eb;
  canonical TeX/PDF pair is clean and only this own registry is dirty for the
  final handoff and lease release
writing (exact paths): completed document checkpoint writes only
  docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex and
  its matching PDF; this report writes only this branch registry; all write
  and process leases are now released
expected declarations or document claims: human-readable counterparts for
  exactly the six accepted compact Lambert-W declarations, plus the existing
  corrected-equivalence theorem needed to print the corrected ratio-one
  formula; no arbitrary-multiplier, cluster-set, liminf, limsup, or numerical
  extrema claim
completed commits: 8d928a55f (coordinator source integration and validated
  tree), 180fc3c3e (feature merge/preservation checkpoint), and 2546fe21b
  (settled primary TeX/PDF pair)
validated (exact command, SHA/state, exit code): coordinator
  `LAKE_JOBS=1 lake build +FabiusFunction.FabiusSharpAsymptotic` at
  8d928a55f, 3891 jobs, exit 0, inherited linter only; three sequential
  sidecar pdflatex passes at the exact 2546fe21b source content, all exit 0,
  final 59-page artifact with settled references, embedded fonts, clean text
  checks, and clean raster inspection of every changed page
not yet validated: no new Lean/Lake invocation was attempted after the
  coordinator's accepted gate; the mathematically stronger cluster-set and
  liminf/limsup results remain deliberately outside canonical theorem-status
  prose until they receive explicit Lean wrappers
requested integration or lease: review and integrate document commit
  2546fe21b together with this registry handoff; no new source, document,
  build, facade, root, coordination, coverage, walkthrough, frontier, or
  aggregate lease is requested; release the primary-document and EVO TeX/PDF
  ownership now
conflicts / dependencies: none.  The feature branch merged the exact active
  lease base, the canonical starting TeX/PDF hashes matched the board, and no
  excluded path was touched
next bounded step: commit and push this registry-only release to the feature
  branch, notify the coordinator, and remain read-only pending disposition
```
