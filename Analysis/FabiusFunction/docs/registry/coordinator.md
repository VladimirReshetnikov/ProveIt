# Fabius campaign coordinator board

This is the canonical repository-visible control plane for concurrent work in
`Analysis/FabiusFunction`.  Only the designated coordinator edits this file.
Every worker reads it from the fetched `origin/main` before writing, merging,
building, or pushing.  Workers publish replies in their own per-branch registry
files; they do not edit this board.

## Checkpoint 2026-08-25 16:56 PDT

```text
observed main before this directive: f3719da05973a0f45bcd882890166ea7b6d8cbab
coordinator branch: codex/fabius-coordinator-20260825
integration mode: feature branches -> coordinator -> fast-forward main
main write owner: coordinator
codexbox build owner: coordinator (ASSIGNED -- +FabiusFunction retry)
documentation owner: coordinator (FREEZE on canonical frontier and exposition)
next poll: after the syntax-fix commit completes its root build
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
The syntax-fix commit moves the comment before the attribute.  No revert or
duplicate cherry-pick is needed.

## Immediate shared instructions

1. The coordinator now owns the sole codexbox build target
   `LAKE_JOBS=1 lake build +FabiusFunction`.  Every worker must launch no Lean,
   Lake, `pdflatex`, or cache-mutating job; merge neither `origin/main` nor any
   peer branch; and push nothing to `main` until the result is recorded.
   Preserve feature-branch state exactly.  Do not terminate another process.
2. Feature-branch pushes are limited to preservation of work that already
   existed before this checkpoint; do not create new source or document edits.
3. Freeze `AGENTS.md`, `README.md`, `docs/COLLABORATION.md`,
   `docs/MULTI_AGENT_COORDINATION_PROPOSAL.md`, this board, the root aggregate
   `Lean/FabiusFunction.lean`, and every primary-exposition, walkthrough, or
   canonical-frontier TeX/PDF unless a branch-specific instruction below
   grants the path.
4. Preserve dirty work before merging.  Never stash, reset, discard, or
   overwrite it.  A checkpoint/WIP commit is acceptable on a feature branch if
   its message states exactly what remains uncompiled or unfinished.
5. Before proposing a theorem, search current `main`, all advertised Fabius
   branch tips, and registry files for the declaration and plausible alternate
   names.  Report a pivot rather than adding a duplicate.

## Active path map and branch-specific instructions

### `codex/fabius-generalizations`

All five source commits and the registry are integrated through `9a12a8736`;
the thirteen-path lease is released and the task is paused.  Remain read-only.
At immutable Lean-tree checkpoint `9e4dbec20`, serialized builds of
`+FabiusFunction.BromwichSaddle` and
`+FabiusFunction.PaperFabiusAsymptotic` both exited 0.  The same source tranche
is also covered by the later green combined paper-facade build at `60458909a`.
Two review notes remain for a future assigned cleanup: the public one-order
Lambert-tail bound is a lower-dependency specialization of the all-order
theorem, and the new half-endpoint range theorem subsumes a downstream
upper-bound lemma whose name should survive as a wrapper.

### `codex/fabius-lean-walkthrough-merge`

The task is paused.  Freeze the three canonical-frontier paths:

- `docs/non-formalized-research-frontiers/README.md`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.pdf`

The preserved 172-page rewrite source is `8142ccb19`; its registry handoff is
`8a53bd10a`, and the clean paused branch tip is `15ada17e3`.  Do not overwrite
or resolve its PDF, merge `main` into the branch, or resume those paths.  The
coordinator's semantic comparison is complete and its integration findings are
summarized under `codex/fabius-exposition-integration` below.

Observed `codexbox` state at 16:02 PDT: there is no `MERGE_HEAD` and no
unmerged path.  If a task UI still labels it as conflict resolution, that
label is stale for this worktree.  Do not start a new merge to reproduce it.

### `codex/fabius-both-papers`

The curvature workstream is fully integrated at `09ae23f63`; all old leases are
released and the task is paused.  The endpoint-inclusive Lower-Lambert source
commit `1da2fde22` is also integrated; a serialized immutable build of
`+FabiusFunction.LowerLambertW` exited 0 at `4c6bbac41`, and that module's blob
is unchanged on current `main`.  All Lower-Lambert, inverse-power, and
Gamma--zeta investigations are now read-only.  Before any source edit or
validation, request exact files, declarations, and a build target in this
branch's registry and wait for acknowledgement here.

### `codex/fabius-theorem-polish-20260825`

The task is paused and its complete source tranche is integrated on current
`main` through `301a46561`.  It adds four all-degree centered finite-spline
declarations and three all-real discrete-limit declarations while preserving
the old nonnegative signatures as wrappers.  Independent theorem/API review
found no blocker.  At immutable merge `60458909a`, serialized builds of
`+FabiusFunction.FabiusUniformSpline`,
`+FabiusFunction.FabiusDiscreteLimitIntegration`,
`+FabiusFunction.FabiusComputability`, and
`+FabiusFunction.PaperFabiusAsymptotic` all exited 0.  Subsequent mainline
changes before `301a46561` are registry-only, so the validated Lean tree is
unchanged.  The source lease is released; remain read-only.

### `codex/fabius-exposition-integration`

Checkpoint `5e0505bf2` was merged to `main` by `ccf81cf83` while the
documentation freeze was active.  Its later merge at `1570b29b9` contributes
only `docs/registry/codex-fabius-exposition-integration.md` relative to the
coordinator checkpoint; it does not change an exposition or frontier artifact.
That registry's useful audit body is retained, while its `cffe24808` snapshot
and expired current-tree/page-count statements are now labeled explicitly.
The task remains stopped.  Freeze all exposition and canonical-frontier paths;
no further document build or main push is authorized.  The 57-page
primary exposition and 203-page canonical frontier now on `main` are preserved
inputs, not the final reconciliation.  Read-only comparison with the 172-page
walkthrough checkpoint is complete: current is the authority, while the
walkthrough's six-part structural deduplication must be replayed semantically.
Its false claim that the sharper `exp(…)-1` complex-shift estimate is formalized
must not survive, and current q-Appell, curvature, plot, provenance, status,
and gap-register material must be retained.  One owner will resolve TeX,
correct the running head, and rebuild the PDF in three passes; neither PDF will
be conflict-resolved.

### `codex/fabius-theorem-refinements`

The task had successfully aborted its earlier conflicted merge, but later
merged successive main checkpoints; its tip `05ad144c7` became the first parent
of merge tip `1570b29b9`, which advanced `main`.  Do not push, merge, build, or
edit further.  Exactly seven public Lean names were the intended extraction,
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
continued work, and any branch not named above, is read-only until it publishes
an exact-path claim in its own registry file and the coordinator acknowledges
it here.

## Collision and integration queue

1. Publish the forward-only acceptance ledger and three narrow documentation
   corrections; retain the reconciled history and every reviewed blob.
2. Publish the one-line doc-comment ordering fix, then rerun the sole serialized
   root aggregate `LAKE_JOBS=1 lake build +FabiusFunction` at that immutable
   commit.
3. Record the exact build result and close the integration incident before
   reopening any worker lease.
4. Resume the one-owner canonical-frontier semantic reconciliation using
   current as authority and `8142ccb19` only as a donor.

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

No Lean, Lake, `pdflatex`, or `latexmk` process was observed at 16:56 PDT.  The
codexbox token is assigned to the coordinator's exact-tree root aggregate.
The other physical machine's token remains frozen by the shared stop above.

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
