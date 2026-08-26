# Fabius campaign coordinator board

This is the canonical repository-visible control plane for concurrent work in
`Analysis/FabiusFunction`.  Only the designated coordinator edits this file.
Every worker reads it from the fetched `origin/main` before writing, merging,
building, or pushing.  Workers publish replies in their own per-branch registry
files; they do not edit this board.

## Checkpoint 2026-08-25 17:21 PDT

```text
observed main before this directive: 893d4c25d81740b7b695f72bc364eed941932ca1
coordinator branch: codex/fabius-coordinator-20260825
integration mode: feature branches -> coordinator -> fast-forward main
main write owner: coordinator
codexbox build owner: coordinator (IDLE -- reserved, no worker target)
EVO build owner: codex/fabius-exposition-integration (TeX only, staged below)
documentation owner: codex/fabius-exposition-integration (frontier paths only)
next poll: after the semantic frontier source checkpoint is pushed
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
   `docs/MULTI_AGENT_COORDINATION_PROPOSAL.md`, this board, the root aggregate
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

The registry claim at `0cb92989d`, synchronized with this board at feature tip
`f1b33700b`, is the first advertised claim for
`Lean/FabiusFunction/GlobalExtension.lean`.  The path is now owned by this
branch until its source checkpoint or release.  The bounded tranche may add
`extendedFabius_natCast_eq_ite` and
`iteratedDeriv_extendedFabius_natCast_eq_zero_iff`, packaging the existing
even/odd knot formulas and global derivative formula without changing existing
public signatures.  Write only that source file and this branch's registry;
leave downstream special cases and all human-document paths untouched.  Push
an explicitly unvalidated source checkpoint.  The codexbox token remains
coordinator-reserved, so launch no Lean, Lake, TeX, or PDF process.

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

The next ordinary claim is advertised at feature tip `ca387fea0` for exactly:

- `Lean/FabiusFunction/NegativeLaplace.lean`;
- `Lean/FabiusFunction/LaplaceMoments.lean`;
- `Lean/FabiusFunction/NegativeLaplaceDerivatives.lean`; and
- `Lean/FabiusFunction/NegativeLaplaceVertical.lean`.

No competing claim touches these four paths, so authoring may proceed after a
clean merge of current `origin/main`; all other workers now treat them as
claimed.  Preserve the exact public signatures of
`generatingFunction_neg_pos` and `fabiusLaplaceMoment_zero_pos` while moving
their proofs to the upstream-most natural modules.  The bounded tranche may add
the advertised global generating-function positivity, all-real zeroth Laplace
moment, normalized-moment value/derivative, and global smoothness/continuity
APIs, then reduce the old positive-half-line results to compatibility
corollaries.  Exclude the finite-`q` witness and every human-document path.
Write only these four source files and the branch registry, and push an
explicitly unvalidated checkpoint.  No EVO build token is granted while the
frontier owner holds that host lane.

### `codex/fabius-shifted-prefix-grid`

The registry-only claim at `6fb8dc8e9`, refreshed with main at feature tip
`11cff7386`, is the first advertised claim for
`Lean/FabiusFunction/ThueMorseGenerating.lean`.  It is an ordinary one-file
source claim with no overlap against the active frontier lease or another
advertised source claim, so authoring may proceed under the open protocol.  All
other workers now treat this source path as claimed by this branch.

Fetch this board and merge current `origin/main` into the clean/checkpointed
feature branch before editing.  The bounded tranche may add the generic
`shiftedPrefixGridValue` family and its zero/one bridges, forward-difference,
scaled-difference, equation, and positive-level equation APIs.  Preserve the
two existing public grid definitions and all eight existing recurrence theorem
statements and attributes exactly as compatibility wrappers; do not include
endpoint, polygon, convergence, or deferred polynomial-calculus work.  Write
only this source file and the branch's own registry, commit frequently, and
push only the feature branch.

No EVO build token is granted.  Mark the source checkpoint unvalidated and
request serialized validation after it is pushed; do not launch Lean, Lake,
TeX, or PDF tools while the exposition branch owns that host token.

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

The clean feature tip `47f5c368e` is an ancestor of current main.  First fetch
and fast-forward the clean feature branch to this board; do not create a merge
commit and do not proceed if a tracked path is dirty or any path is unmerged.
The sole cleanliness exception is the two already registry-recorded untracked
`*_build.pdf` copies: they may remain only if their SHA-256 values still match
the corresponding committed PDFs exactly and no other untracked path exists.
Leave those copies untouched during stage one; a mismatch or any additional
dirty path blocks work and must be reported in the branch registry.  Use
current main's 203-page source as semantic authority and `8142ccb19` only as a
donor.  Leave the root README and every primary/walkthrough path untouched.

The source checkpoint must preserve current q-Appell/Bromwich material,
sparse-bit qualification, random-law warning, Thue--Morse cancellation and
plots, all twelve provenance rows, curvature/inverse-endpoint results, and the
complete gap register.  Preserve the formalization boundary: Lean proves the
plain exponential complex-shift bound, while the sharper `exp(…)-1` estimate
and its `p = 2` edge case remain frontier obligations.  Replay the donor's
six-part structural handoffs, normalized-mass definition and real-log domain,
finite-level floor-profile certificates and dilation notation, alternate
recurrence path, and specialist open-obligation organization without
duplicating mathematics already present.  Organize the result as six thematic
syntheses plus the post-audit gap register.

Stage one is TeX/README only: run conflict-marker, label/reference, provenance,
status-wording, and changed-cluster audits; commit and push the feature source
checkpoint.  Stage two may then use the sole EVO token for exactly three
`pdflatex` passes, correct the page-10 running head, require settled references
and citations, no duplicate labels or overfull boxes, and inspect every changed
cluster.  Commit the regenerated PDF and exact evidence to the feature branch;
never select either predecessor PDF or push `main`.  The 57-page primary
exposition remains frozen until this frontier tranche is reviewed and
integrated.

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

1. Receive and audit the semantic frontier TeX/README checkpoint before any PDF
   is regenerated.
2. In parallel, receive and review the shifted-prefix-grid, natural-knot, and
   all-real Laplace source checkpoints; validate them only through subsequently
   assigned host tokens.
3. Receive the three-pass PDF/evidence checkpoint, then integrate the complete
   frontier tranche through the coordinator.
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

No Lean, Lake, `pdflatex`, or `latexmk` process was observed at 17:00 PDT.  The
codexbox token is idle and coordinator-reserved.  The EVO token is reserved to
the exposition branch's staged frontier build.  Other branches may edit,
checkpoint, and push under the open protocol, but may not run validation tools
until this board assigns the applicable physical-host token.

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
