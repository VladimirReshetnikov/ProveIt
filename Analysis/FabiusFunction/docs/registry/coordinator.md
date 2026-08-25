# Fabius campaign coordinator board

This is the canonical repository-visible control plane for concurrent work in
`Analysis/FabiusFunction`.  Only the designated coordinator edits this file.
Every worker reads it from the fetched `origin/main` before writing, merging,
building, or pushing.  Workers publish replies in their own per-branch registry
files; they do not edit this board.

## Checkpoint 2026-08-25 16:28 PDT

```text
observed main before this directive: 301a46561dd6495a2b39c683c009950b5e8aa87d
coordinator branch: codex/fabius-coordinator-20260825
integration mode: feature branches -> coordinator -> fast-forward main
main write owner: coordinator
codexbox build owner: coordinator (IDLE -- no Lean/Lake/TeX process observed)
documentation owner: coordinator (FREEZE on canonical frontier and exposition)
next poll: before the isolated theorem-refinements extraction is promoted
```

The curvature tranche, five-commit generalizations tranche, lower-Lambert
endpoint tranche, exposition checkpoint `5e0505bf2`, and theorem-polish tranche
are now on `main`.  Their former source leases are released.  The complete
current Lean tree is byte-identical to immutable validated merge `60458909a`
except for registry-only commits, and its focused and paper-facade gates are
green.  The two competing canonical-frontier documents have not yet been
semantically reconciled; neither preserved PDF is authoritative.

## Immediate shared instructions

1. The codexbox build token is idle but reserved to the coordinator.  Launch
   no Lean, Lake, `pdflatex`, or cache-mutating job there until this board names
   a worker and exact target.  Do not terminate another worktree's process.
2. Push only named feature branches.  Do not push directly to `main` during
   collision recovery.
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
documentation freeze was active.  Freeze all exposition and canonical-frontier
paths now; no further document build or main push is authorized.  The 57-page
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

Remote tip `1b2cd37dd` has thirteen commits not on the observed campaign base
and touches several hot Lean and documentation paths.  Do not merge or push it
to `main` wholesale.  Preserve and push the feature tip, then update its own
registry with a declaration-by-declaration list of results still absent from
current `main`.  The coordinator will extract reviewed, nonduplicate commits.

**Recovery directive `FABIUS-R001` is satisfied.**  The attempted wholesale
merge was cleanly aborted; do not retry it.  The preserved branch remains
read-only.  A declaration-by-declaration audit found exactly seven public Lean
names absent from current `main`, all in commit `a95bd1913` and all confined to
`FabiusQBinomialTaylor.lean`: translated Thue--Morse polynomial coefficient,
zero, self-value, zero-iff, natural-degree, leading-coefficient, and degree
APIs.  The coordinator will replay only that source diff on a fresh branch and
build it.  README, registry, control-plane, TeX, PDF, and every other stale
branch change are excluded.

### Claude Fabius branches and any unlisted branch

The observed Claude asymptotic, documentation, theorem, and non-elementarity
tips are ancestors of the campaign base.  Their old leases are closed.  Any
continued work, and any branch not named above, is read-only until it publishes
an exact-path claim in its own registry file and the coordinator acknowledges
it here.

## Collision and integration queue

1. Publish this refreshed control-plane checkpoint; all paused workers remain
   read-only and the codexbox build token remains reserved.
2. Extract only the reviewed `a95bd1913` source diff from the stale refinements
   branch onto current `main`; run its focused module and paper-facade gates.
3. Reconcile the canonical frontier semantically in TeX under one owner using
   current as authority and `8142ccb19` as the structural-dedup source; rebuild
   its PDF only after source validation.
4. Review the primary exposition and walkthrough artifacts after the canonical
   frontier is stable.
5. Run one serialized root aggregate build at an immutable combined SHA after
   the extracted theorem API and document source settle.

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

No Lean, Lake, `pdflatex`, or `latexmk` process was observed at 16:28 PDT.  The
codexbox token is idle but remains coordinator-reserved.  A build owner on the
other physical machine records its independent token in its branch registry.

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
