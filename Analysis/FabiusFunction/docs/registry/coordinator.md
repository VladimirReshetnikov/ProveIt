# Fabius campaign coordinator board

This is the canonical repository-visible control plane for concurrent work in
`Analysis/FabiusFunction`.  Only the designated coordinator edits this file.
Every worker reads it from the fetched `origin/main` before writing, merging,
building, or pushing.  Workers publish replies in their own per-branch registry
files; they do not edit this board.

## Checkpoint 2026-08-25 16:42 PDT

```text
observed main before this directive: 1570b29b9017fc9543cfe27221bec72ff15bdfdc
coordinator branch: codex/fabius-coordinator-20260825
integration mode: feature branches -> coordinator -> fast-forward main
main write owner: coordinator
codexbox build owner: coordinator (LOCKED -- integration incident audit)
documentation owner: coordinator (FREEZE on canonical frontier and exposition)
next poll: after the 28-commit unreviewed-main delta is dispositioned
```

The previously approved curvature, generalizations, lower-Lambert,
exposition, and theorem-polish tranches remain on `main`.  At 16:35--16:39,
however, two paused feature histories advanced `main` from `f74396e5a` to
`1570b29b9` by 28 commits.  The exposition branch contributes only its registry
relative to the coordinator checkpoint, but the theorem-refinements lineage
bundled the reviewed translated-polynomial source with sixteen other changed
paths, including a frozen TeX/PDF pair, root aggregate, facades, and unrelated
Lean prose/options.  Those additional paths are present but not yet accepted;
they are under read-only source, document, and topology audit.

## Immediate shared instructions

1. **Urgent stop:** launch no Lean, Lake, `pdflatex`, or cache-mutating job;
   merge neither `origin/main` nor any peer branch; and push nothing to `main`
   until this incident checkpoint is superseded.  Preserve feature-branch
   state exactly.  Do not terminate another worktree's process.
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
merged successive main checkpoints and advanced `main` at `05ad144c7` with its
entire stale lineage.  Do not push, merge, build, or edit further.  Exactly
seven public Lean names were the intended extraction, all from `a95bd1913` in
`FabiusQBinomialTaylor.lean`: translated Thue--Morse polynomial coefficient,
zero, self-value, zero-iff, natural-degree, leading-coefficient, and degree
APIs.  The source blob now on `main` matches the independently extracted blob
at coordinator branch `a6fa59157` exactly; serialized focused and
`PaperFabiusAsymptotic` builds of that extraction both exited 0.

The remaining theorem-refinements delta is not accepted merely because Git
merged it.  Nine other Lean/root/facade paths, the non-elementarity TeX/PDF,
coverage/audit files, and three registries are under read-only audit.  No one
may revert, overwrite, rebuild, or expand those paths until the coordinator
publishes a path-by-path disposition.

### Claude Fabius branches and any unlisted branch

The observed Claude asymptotic, documentation, theorem, and non-elementarity
tips are ancestors of the campaign base.  Their old leases are closed.  Any
continued work, and any branch not named above, is read-only until it publishes
an exact-path claim in its own registry file and the coordinator acknowledges
it here.

## Collision and integration queue

1. Publish this emergency stop checkpoint and prevent any further mainline,
   build-lane, or document movement.
2. Complete the three independent read-only audits of `f74396e5a..1570b29b9`:
   Lean truth/API/provenance, documentation/PDF claims, and merge topology.
3. Retain the exact reviewed `FabiusQBinomialTaylor.lean` blob; disposition
   every other landed path explicitly, using new commits only and never force.
4. Validate the resulting current-main Lean tree at one immutable SHA before
   reopening any worker lease.
5. Resume the one-owner canonical-frontier semantic reconciliation only after
   the integration incident is closed.

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

No Lean, Lake, `pdflatex`, or `latexmk` process was observed at 16:42 PDT.  The
codexbox token is locked during incident audit.  The other physical machine's
token is also frozen by the urgent shared stop above.

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
