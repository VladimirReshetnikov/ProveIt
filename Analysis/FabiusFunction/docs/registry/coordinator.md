# Fabius campaign coordinator board

This is the canonical repository-visible control plane for concurrent work in
`Analysis/FabiusFunction`.  Only the designated coordinator edits this file.
Every worker reads it from the fetched `origin/main` before writing, merging,
building, or pushing.  Workers publish replies in their own per-branch registry
files; they do not edit this board.

## Checkpoint 2026-08-25 18:44 PDT

```text
observed main before this directive: ba2be1b782b8aa77979c40eb5c43a1b102e20b81
coordinator branch: codex/fabius-coordinator-20260825
integration mode: feature branches -> coordinator -> fast-forward main
main write owner: coordinator
codexbox build owner: coordinator (IDLE -- reserved, no worker target)
EVO build owner: codex/fabius-exposition-integration (frontier pdflatex only)
documentation owner: codex/fabius-exposition-integration (frontier paths only)
next poll: after the three-pass frontier PDF/evidence checkpoint
```

The previously approved curvature, generalizations, lower-Lambert,
exposition, and theorem-polish tranches remain on `main`.  One merge tip
incorporating two paused feature histories advanced `main` from `f74396e5a` to
`1570b29b9`: 28 commits became newly reachable and produced an 18-path net
delta.  Three independent audits are complete.  The exact translated-polynomial
source, all nine non-semantic Lean/root/facade deltas, the isolated
non-elementarity TeX/PDF pair, the audit fence repair, and the two Claude
registry updates are accepted.  The exposition and theorem-refinements
registries are retained with snapshot corrections, and the sole coverage-link
defect is fixed forward.  The first exact root build then caught one parse-only
defect: a new `partialSum_smul` doc comment sat between `@[simp]` and `theorem`.
The syntax-fix commit moves the comment before the attribute.  The retry at
immutable `9887ea584` passed the complete `+FabiusFunction` aggregate (4008
jobs, exit 0).  The integration incident is closed; no revert or duplicate
cherry-pick is needed.

## Immediate shared instructions

1. **Feature-branch work is open.**  Any worker may make local changes, commit
   frequently, and push its own named feature branch.  Before editing ordinary
   paths, push a `SYNC Fabius` claim in that branch's registry naming the exact
   paths and expected declarations or document claims; fetch/read this board
   and inspect advertised registries/tips for overlap and plausible duplicate
   declarations.  If the claim is nonoverlapping and avoids the serialized
   paths below, work may begin without coordinator acknowledgement.  Push
   feature branches only; the coordinator is the sole `main` writer.  Never
   force.
2. The codexbox build token is idle and coordinator-reserved.  On EVO, only the
   exposition branch may use the host token, and only for the staged TeX build
   authorized below.  Other workers may edit and commit unvalidated work, but
   launch no Lean, Lake, TeX, PDF, or cache-mutating process; label such commits
   and registry reports `Not yet validated`.  Do not terminate another process.
3. The following remain serialized and require an explicit board grant:
   `AGENTS.md`, `README.md`, `docs/COLLABORATION.md`,
   `docs/MULTI_AGENT_COORDINATION_PROPOSAL.md`, `docs/PAPER_COVERAGE.md`,
   `docs/AUDIT_FINDINGS.md`, this board, the root aggregate
   `Lean/FabiusFunction.lean`, and every primary-exposition, walkthrough, or
   canonical-frontier TeX/PDF path.  Any path marked hot, frozen, or
   single-owner below is also unavailable to ordinary claims.  The active
   frontier lease remains exclusive to `codex/fabius-exposition-integration`.
4. Preserve dirty work before merging.  Never stash, reset, discard, or
   overwrite it.  A checkpoint/WIP commit is acceptable on a feature branch if
   its message states exactly what remains uncompiled or unfinished.  After a
   clean/checkpointed push and a fresh board read, workers may merge
   `origin/main` into their own feature branches.  Resolve only conflicts
   wholly within an uncontested claim; report and stop on serialized, generated,
   or multiply claimed paths.
5. Before proposing a theorem, search current `main`, all advertised Fabius
   branch tips, and registry files for the declaration and plausible alternate
   names.  Report a pivot rather than adding a duplicate.
6. A claim expansion follows the same protocol: advertise and push the added
   exact paths before editing them.  If two advertised claims overlap, neither
   worker edits the overlap until one pivots or this board assigns ownership;
   nonoverlapping portions may continue.
7. Push preservation checkpoints promptly.  The coordinator may prune a
   worktree after seven days without activity, even when it is dirty.  Pushed
   commits and remote branches survive pruning; uncommitted changes do not.

## Active path map and branch-specific instructions

### `codex/fabius-generalizations`

All five source commits and the registry are integrated through `9a12a8736`;
the thirteen-path lease is released and the prior task is complete.  This
branch may begin new ordinary, nonoverlapping work under the shared protocol;
the released paths are not implicitly re-leased.
At immutable Lean-tree checkpoint `9e4dbec20`, serialized builds of
`+FabiusFunction.BromwichSaddle` and
`+FabiusFunction.PaperFabiusAsymptotic` both exited 0.  The same source tranche
is also covered by the later green combined paper-facade build at `60458909a`.
Two review notes remain for a future assigned cleanup: the public one-order
Lambert-tail bound is a lower-dependency specialization of the all-order
theorem, and the new half-endpoint range theorem subsumes a downstream
upper-bound lemma whose name should survive as a wrapper.

### `codex/fabius-lean-walkthrough-merge`

The prior task is paused.  This branch may begin unrelated ordinary work under
the shared protocol, but the three canonical-frontier paths remain exclusively
leased elsewhere:

- `docs/non-formalized-research-frontiers/README.md`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.pdf`

The preserved 172-page rewrite source is `8142ccb19`; its registry handoff is
`8a53bd10a`, and the clean paused branch tip is `15ada17e3`.  Do not overwrite
or resolve its PDF or resume those paths.  Before unrelated work, fetch and
merge current `main` only from a clean/checkpointed state under the shared
rules.  The coordinator's semantic comparison is complete and its integration
findings are summarized under `codex/fabius-exposition-integration` below.

Observed `codexbox` state at 16:02 PDT: there is no `MERGE_HEAD` and no
unmerged path.  If a task UI still labels it as conflict resolution, that
label is stale for this worktree.  Do not start a new merge to reproduce it.

### `codex/fabius-both-papers`

The curvature workstream is fully integrated at `09ae23f63`; all old leases are
released and the prior task is complete.  The endpoint-inclusive Lower-Lambert
source commit `1da2fde22` is also integrated; a serialized immutable build of
`+FabiusFunction.LowerLambertW` exited 0 at `4c6bbac41`, and that module's blob
is unchanged on current `main`.  All Lower-Lambert, inverse-power, and
Gamma--zeta leases are released.  This branch may begin new ordinary work after
advertising exact files and declarations in its registry; it must still wait
for a board token before any validation process.

The natural-knot tranche is integrated through coordinator reconciliation
`068fc1be5`.  It adds exactly `extendedFabius_natCast_eq_ite` and
`iteratedDeriv_extendedFabius_natCast_eq_zero_iff` in
`Lean/FabiusFunction/GlobalExtension.lean`; existing signatures and downstream
special cases remain unchanged.  Independent proof/API review found no
implemented Lean duplicate and no theorem blocker.  The coordinator repaired
three elaboration sites at `62f4142a9`, then reconciled the worker's odd-witness
correction and registry at `068fc1be5`.

At immutable Lean tree `068fc1be5`, serialized one-job builds of
`+FabiusFunction.GlobalExtension` (2765 jobs) and
`+FabiusFunction.Paper06487` (3244 jobs) both exited 0.  The latter transitively
covers `PaperStatements` and `Paper06487Supplement`; `git diff --check` and the
forbidden-declaration scan are clean.  The `GlobalExtension.lean` lease is
released.  The branch may begin another ordinary nonoverlapping claim, but
must still receive a host token before running any validation process.

Clean feature tip `c41a52283` now publishes four additional, explicitly
unvalidated source units on top of current main:

- dyadic-cast relocation `09b360531` across
  `Lean/FabiusFunction/GlobalDyadic.lean` and
  `Lean/FabiusFunction/OriginalPaperSupplement.lean`;
- strict Gamma--zeta sign API `ec23d663f` / `991add419` in
  `Lean/FabiusFunction/BoseFinitePartIntegral.lean`;
- inverse-power cast bridge `9458b1949` in
  `Lean/FabiusFunction/DyadicAnalytic.lean`;
- periodic dyadic-exponential helper consolidation `c7c2321bc` across
  `Lean/FabiusFunction/PeriodicRegularity.lean` and
  `Lean/FabiusFunction/PeriodicSmooth.lean`.

`GlobalExtension.lean` also has a doc-comment-only terminology edit.  These
seven source paths and the branch registry are frozen at `c41a52283` pending
independent review and coordinator-held codexbox validation.  No worker may
claim or modify them, and this branch must not expand the tranche or run Lean,
Lake, TeX, or PDF tools.  It may advertise unrelated ordinary work only after
the frozen tip is preserved and the new claim is disjoint from every listed
path.

### `codex/fabius-theorem-polish-20260825`

The prior task is complete and its complete source tranche is integrated on
current `main` through `301a46561`.  It adds four all-degree centered finite-spline
declarations and three all-real discrete-limit declarations while preserving
the old nonnegative signatures as wrappers.  Independent theorem/API review
found no blocker.  At immutable merge `60458909a`, serialized builds of
`+FabiusFunction.FabiusUniformSpline`,
`+FabiusFunction.FabiusDiscreteLimitIntegration`,
`+FabiusFunction.FabiusComputability`, and
`+FabiusFunction.PaperFabiusAsymptotic` all exited 0.  Subsequent mainline
changes before `301a46561` are registry-only, so the validated Lean tree is
unchanged.  The source lease is released; this branch may begin a new ordinary,
nonoverlapping claim under the shared protocol.

The four-file claim advertised at `ca387fea0` is implemented by source
checkpoint `87c9b00f4` for exactly:

- `Lean/FabiusFunction/NegativeLaplace.lean`;
- `Lean/FabiusFunction/LaplaceMoments.lean`;
- `Lean/FabiusFunction/NegativeLaplaceDerivatives.lean`; and
- `Lean/FabiusFunction/NegativeLaplaceVertical.lean`.

The follow-on claim at `a6091bacf` adds only
`Lean/FabiusFunction/LaplaceMomentBounds.lean`; source checkpoint `efee2a7e1`
extends normalized-moment nonnegativity to every real tilt and intentionally
depends on the four-file tranche's all-real zeroth-moment theorem.  Registry
checkpoints `1d4a88a42` and `5331c74d5` report both tranches, and `909cb359c`
froze further work pending coordinator disposition.  Independent review found
no truth, API, dependency, duplicate, or scope blocker.  Coordinator merge
`0d308188c` then exposed one elaboration-only mismatch in the new global
`ContDiff` proof; `c4bc42f16` fixes it by changing the goal explicitly to the
pointwise quotient before applying `ContDiff.div`, without changing any public
statement.

At the repaired immutable tree, the derivative, vertical, bounds, and
`PaperFabiusAsymptotic` targets all exit 0; the two upstream focused targets
also exit 0 with source blobs unchanged by the repair.  Exact job counts and
the one superseded failed attempt are recorded in the build log and branch
registry.  The five source leases are released.  The branch may begin another
ordinary nonoverlapping claim after reading this board; no EVO validation token
is granted.

### `codex/fabius-shifted-prefix-grid`

The one-file source claim is implemented at checkpoint
`00ff41a5e` in `Lean/FabiusFunction/ThueMorseGenerating.lean`.  It adds the
generic `shiftedPrefixGridValue` family and seven APIs, while preserving the
two public grid definitions and all eight legacy theorem headers and
attributes as compatibility wrappers.  Independent exact source review is
green: the seven declarations are true, the zero/one simp bridges are safe,
the positive-level hypothesis is necessary, every old type and attribute is
unchanged, and no duplicate or competing source claim exists.

The branch then expanded beyond its branch-specific “source file plus own
registry” grant and committed `docs/PAPER_COVERAGE.md` at `dcd5f8a06`.  Preserve
that feature commit for separate review; it was not authorized for `main` by
the registry-first self-claim alone.  Commit `faf1fcaf6` similarly changed
`docs/AUDIT_FINDINGS.md` 53 seconds before checkpoint `148990f0a` explicitly
serialized both files, but still exceeded the earlier exact branch grant.
Pathwise audit nevertheless finds both documentation deltas accurate, so the
coordinator now explicitly accepts them as separate units rather than
discarding useful work.  This is not permission for another expansion.

Feature tip `8ea040921` was clean, synchronized with `148990f0a`, and froze all
prior paths.  Coordinator merge `ae16882d5` integrates that frozen tip.  The
registry now correctly identifies SHA-256 `48C94725...` as the audit patch
hash, not the committed file hash (`507136BA...`, Git blob `3eeb0880...`), and
the coverage map records the immutable validation evidence.

At `ae16882d5`, serialized builds of `+FabiusFunction.ThueMorseGenerating`
(2085 jobs), `+FabiusFunction.ThueMorseApproximation` (3307 jobs),
`+FabiusFunction.ThueMorseExponential` (2086 jobs), and
`+FabiusFunction.PaperKFoldThueMorse` (3327 jobs) all exited 0.  The source
lease is released, while `PAPER_COVERAGE.md` and `AUDIT_FINDINGS.md` return to
campaign-wide serialized status.  The branch may begin a new ordinary,
nonoverlapping claim after reading this board; no EVO build token is granted.

### `codex/fabius-exposition-integration`

Checkpoint `5e0505bf2` was merged to `main` by `ccf81cf83` while the
documentation freeze was active.  Its later merge at `1570b29b9` contributes
only `docs/registry/codex-fabius-exposition-integration.md` relative to the
coordinator checkpoint; it does not change an exposition or frontier artifact.
That registry's useful audit body is retained, while its `cffe24808` snapshot
and expired current-tree/page-count statements are now labeled explicitly.

**Single-owner frontier lease.**  This branch may now write only:

- `docs/non-formalized-research-frontiers/README.md`;
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`;
- its matching `.pdf`; and
- `docs/registry/codex-fabius-exposition-integration.md`.

Stage-one source checkpoint `78260751f` and the audit correction
`23daad436` are pushed; feature tip `e1c087738` is clean and synchronized with
current main `ba2be1b78`.  Its net delta remains exactly the frontier
README/TeX and the branch registry; the committed PDF blob is still identical
to main.  Independent audit accepts the mathematical/formalization boundary,
six-part structure, donor clusters, provenance, labels/references/citations,
gap register, and all four required corrections.  In particular the corrected
TeX SHA-256 is
`8562CF91CDB48132C1DBF127B80886D9EFF8D46057805A200B4579A42E054546`;
the running-head reset occurs once, the removed probability-product label
occurs zero times, both canonical labels occur once, and the two open-ledger
implementation routes are restored.  Static audit reports 986 unique labels,
625 resolved references, 52 unique bibliography keys, 20 resolved citation
targets, 1201 balanced environment pairs, 20 candidates, 20 obligations, and
seven parts; `git diff --check` is green and no path is unmerged.

**Stage-two grant.**  This branch now holds the sole EVO tool token for the
canonical frontier only.  From clean tip `e1c087738`, run exactly three
sequential `pdflatex` passes on
`non-formalized-research-frontiers.tex`; launch no Lean, Lake, `latexmk`, or
other TeX build.  Require settled references and citations, zero duplicate
labels, zero overfull boxes, and no fatal/error diagnostics.  Inspect the
rendered page-10 running head and every changed cluster, record exact command,
tip, log predicates, page count, PDF hash, and visual-inspection evidence in
the branch registry, then commit only the regenerated frontier PDF plus that
registry and push the feature branch.  If any predicate fails, do not perform
a fourth pass or broaden the source edit: preserve the log, report the exact
failure in the registry, and stop for a new board disposition.  Never select a
predecessor PDF or push `main`.

The frontier README/TeX are frozen during stage two, and the 57-page primary
exposition remains fully frozen until the complete frontier tranche is
reviewed and integrated.

### `codex/fabius-theorem-refinements`

The task had successfully aborted its earlier conflicted merge, but later
merged successive main checkpoints; its tip `05ad144c7` became the first parent
of merge tip `1570b29b9`, which advanced `main`.  That incident is closed.  The
branch may sync and begin new ordinary, nonoverlapping work under the shared
protocol, but must not replay or re-extract the integrated tranche.  Exactly
seven public Lean names were the intended extraction,
all from `a95bd1913` in
`FabiusQBinomialTaylor.lean`: translated Thue--Morse polynomial coefficient,
zero, self-value, zero-iff, natural-degree, leading-coefficient, and degree
APIs.  The source blob now on `main` matches the independently extracted blob
at coordinator branch `a6fa59157` exactly; serialized focused and
`PaperFabiusAsymptotic` builds of that extraction both exited 0.

The pathwise audit accepts the other nine Lean/root/facade blobs: five contain
only accurate comments and four comment-only paper facades add only
`set_option autoImplicit false`; no declaration, proof, signature, import,
instance, or API changes.  Exact compilation found and fixes forward the sole
syntax defect in that prose tranche by placing the `partialSum_smul` doc comment
before its existing `@[simp]` attribute.  It also accepts the 14-page
non-elementarity TeX/PDF pair from semantic merge `1b2cd37dd`, the missing
audit code fence, and the two SHA-bound Claude registry updates.  The dead
coverage link and stale current-state wording in both Codex registries are
fixed forward in the coordinator acceptance commit.  The branch history and
content are retained; do not cherry-pick `a6fa59157`, whose source is already
present.

### Claude Fabius branches and any unlisted branch

The observed Claude asymptotic, documentation, theorem, and non-elementarity
tips are ancestors of the campaign base.  Their old leases are closed.  Any
continued work, and any branch not named above, may begin after it pushes an
exact-path/declaration claim in its own registry and verifies that the claim is
ordinary and nonoverlapping.  No coordinator acknowledgement is needed unless
a requested path is serialized, hot, frozen, single-owner, or already claimed.

## Collision and integration queue

1. Receive and audit the authorized three-pass frontier PDF/evidence checkpoint.
2. Complete the independent review and serialized codexbox validation of the
   four frozen both-papers source units at `c41a52283`.
3. Integrate the complete green frontier tranche through the coordinator.
4. Only after the frontier stabilizes, assign the primary exposition's four
   narrow citation/attribution corrections and matching PDF rebuild.

## Build-token log

At 15:45 PDT the coordinator observed two concurrent jobs on `codexbox`:

- worktree `042c`: `lake build +FabiusFunction.FabiusFullAsymptoticExpansion`;
- worktree `/home/codex/src/Proofs`: `lake env lean /tmp/LowerLambertWPrototype.lean`.

Those jobs exited, but the same worktree later launched concurrent
`LowerLambertWPrototype` and `FabiusInversePowerBridgeAudit` jobs.  After they
exited, the coordinator started the sole immutable integration build at
`9e4dbec20`; a new unassigned `FabiusGammaZetaSignAudit` job then appeared.
The coordinator stopped only its own build (exit `130`) and makes no validation
claim from that interrupted attempt.

After the lane became quiet, the coordinator held the token and completed
these serialized immutable validations:

- at `9e4dbec20`: `+FabiusFunction.BromwichSaddle` and
  `+FabiusFunction.PaperFabiusAsymptotic`, both exit 0;
- at `4c6bbac41`: `+FabiusFunction.LowerLambertW`, exit 0;
- at `60458909a`: `+FabiusFunction.FabiusUniformSpline`,
  `+FabiusFunction.FabiusDiscreteLimitIntegration`,
  `+FabiusFunction.FabiusComputability`, and
  `+FabiusFunction.PaperFabiusAsymptotic`, all exit 0.
- at source-only extraction `a6fa59157`:
  `+FabiusFunction.FabiusQBinomialTaylor` (3320 jobs) and
  `+FabiusFunction.PaperFabiusAsymptotic` (3957 jobs), both exit 0.

At acceptance commit `f3719da05`, the first
`LAKE_JOBS=1 lake build +FabiusFunction` attempt reached 4007/4008 completed
jobs but exited 1 because `SaddleExpansionAlgebra.lean:358` placed a doc comment
after `@[simp]`; Lean expected the declaration immediately after the attribute.
All other jobs in that invocation passed.  The retry is assigned only after the
comment is moved before the attribute in a new immutable commit.

At syntax-fix commit `9887ea584`, the retry
`LAKE_JOBS=1 lake build +FabiusFunction` completed all 4008 jobs and exited 0.
This is exact-tree validation of every current Lean module and closes the
integration incident.

At natural-knot reconciliation `068fc1be5`, the coordinator held the codexbox
token and ran two separate `LAKE_JOBS=1` targets:

- `+FabiusFunction.GlobalExtension` completed 2765 jobs, exit 0;
- `+FabiusFunction.Paper06487` completed 3244 jobs, exit 0 and transitively
  covered `PaperStatements` plus `Paper06487Supplement`.

For the all-real Laplace tranche, `+FabiusFunction.NegativeLaplace` (2831
jobs) and `+FabiusFunction.LaplaceMoments` (2857 jobs) exited 0 at merge
`0d308188c`.  The first `+FabiusFunction.NegativeLaplaceDerivatives` attempt
then exited 1 on a definitional folding mismatch in the new `ContDiff` proof;
it supplied no validation evidence.  After the narrow elaboration repair at
`c4bc42f16`, that target completed 2858 jobs and exited 0.  At the same repaired
tree, `+FabiusFunction.NegativeLaplaceVertical` (3194 jobs),
`+FabiusFunction.LaplaceMomentBounds` (3417 jobs), and
`+FabiusFunction.PaperFabiusAsymptotic` (3957 jobs) all exited 0.  The two
upstream source blobs are unchanged by the repair.

At shifted-grid merge `ae16882d5`, the coordinator retained the codexbox token
and ran four separate targets: `+FabiusFunction.ThueMorseGenerating` (2085
jobs), `+FabiusFunction.ThueMorseApproximation` (3307 jobs),
`+FabiusFunction.ThueMorseExponential` (2086 jobs), and
`+FabiusFunction.PaperKFoldThueMorse` (3327 jobs).  All exited 0.

Before those green runs, one command launched from the wrong directory was a
no-op, and the first correctly rooted attempt exhausted the filesystem while
creating a fresh `.lake`; it exited 1 and supplied no validation evidence.
The coordinator removed only that generated failed cache, then copied an idle
worktree's dependency cache and reran at the immutable source tree.  During the
worker checkpoint, `/home/codex/src/Proofs` also launched an unassigned
`lake env lean` prototype check; it exited and is not treated as integration
evidence.

No validation process is now running on codexbox.  Its token is idle and
coordinator-reserved.  The sole EVO token is assigned to
`codex/fabius-exposition-integration` for exactly the three frontier
`pdflatex` passes specified above; no other EVO branch may run Lean, Lake,
TeX, PDF, or cache-mutating tools.  Other branches may edit, checkpoint, and
push ordinary claimed work under the open protocol, but may not run validation
tools until this board assigns the applicable physical-host token.

## Worktree maintenance log

With the user's explicit authorization, the coordinator removed two codexbox
worktrees whose last activity was more than one week old and whose processes
were not live:

- clean worktree `97db`, branch `codex/port-foundation-theorems`; committed
  remote tip `8b273f16f` remains available;
- dirty worktree `44ac`, branch `codex/quintic-radical-completeness`; committed
  remote tip `c29cbb447` remains available, but its 12 modified tracked files
  and 3392 untracked files were uncommitted and are unrecoverable.

This recovered enough disk space for the isolated coordinator cache.  Future
week-idle pruning follows the preservation rule above: push even a clearly
labelled WIP checkpoint if the work must survive.

## Worker reply template

Commit this block to your own registry file and push the feature branch:

```text
SYNC Fabius
branch / worktree / machine:
fetched main SHA:
HEAD and dirty paths:
writing (exact paths):
expected declarations or document claims:
completed commits:
validated (exact command, SHA/state, exit code):
not yet validated:
requested integration or lease:
conflicts / dependencies:
next bounded step:
```
