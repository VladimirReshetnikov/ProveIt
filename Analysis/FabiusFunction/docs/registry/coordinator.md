# Fabius campaign coordinator board

This is the canonical repository-visible control plane for concurrent work in
`Analysis/FabiusFunction`.  Only the designated coordinator edits this file.
Every worker reads it from the fetched `origin/main` before writing, merging,
building, or pushing.  Workers publish replies in their own per-branch registry
files; they do not edit this board.

## Checkpoint 2026-08-25 15:56 PDT

```text
observed main before this directive: 22d63a9f74a9dd022b243fc3836930ae94354ff9
coordinator branch: codex/fabius-coordinator-20260825
integration mode: feature branches -> coordinator -> fast-forward main
main write owner: coordinator
codexbox build owner: coordinator (PAUSED -- two pre-existing jobs overlap)
documentation owner: coordinator (FREEZE on canonical frontier and exposition)
next poll: after worker checkpoint pushes or any origin/main advancement
```

The curvature tranche through `09ae23f63` is integrated.  Its former leases are
released.  At this checkpoint the source scan remains free of `sorry`, `admit`,
declared `axiom`, and `opaque`, but this is not a fresh aggregate-build claim.

## Immediate shared instructions

1. Let currently running validation processes finish.  Launch no new Lean,
   Lake, `pdflatex`, or cache-mutating job on `codexbox` until this board names
   a build owner and target.  Do not terminate another worktree's process.
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

Recognized preservation lease, limited to the thirteen already-dirty files:

- `Lean/FabiusFunction/BromwichSaddle.lean`
- `Lean/FabiusFunction/DyadicAnalytic.lean`
- `Lean/FabiusFunction/DyadicCorrectness.lean`
- `Lean/FabiusFunction/EarlyApproximants.lean`
- `Lean/FabiusFunction/FabiusSaddleCentralRadiusAsymptotics.lean`
- `Lean/FabiusFunction/FabiusSaddleReduction.lean`
- `Lean/FabiusFunction/FabiusSaddleTail.lean`
- `Lean/FabiusFunction/FabiusSaddleTailAllOrders.lean`
- `Lean/FabiusFunction/FabiusSharpAsymptotic.lean`
- `Lean/FabiusFunction/FabiusSharpExactReduction.lean`
- `Lean/FabiusFunction/FabiusSharpLambertTransfer.lean`
- `Lean/FabiusFunction/TaylorReduction.lean`
- `Lean/FabiusFunction/ThueMorseBinomialLog.lean`

Do not expand this set.  Let the already-running
`+FabiusFunction.FabiusFullAsymptoticExpansion` build finish and record its
exact HEAD/dirty-state caveat.  Then split the work into the smallest coherent
commits, add or refresh this branch's registry file, push the feature branch,
fetch `main`, and wait for integration review.  Do not push this tranche to
`main` directly.

### `codex/fabius-lean-walkthrough-merge`

Freeze the three dirty canonical-frontier paths now:

- `docs/non-formalized-research-frontiers/README.md`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.pdf`

The worktree is based at `13b84a479`, while `main` has since changed the same
TeX/PDF in the curvature tranche; `codex/fabius-exposition-integration` also
changes them.  Do not overwrite or resolve the PDF.  Preserve the current
172-page rewrite on the feature branch, push its exact SHA, and report its
source inputs and three-pass PDF build evidence in a new branch registry file.
Do not merge `main` into this branch or resume those paths until the coordinator
assigns one semantic TeX integrator.

### `codex/fabius-both-papers`

The curvature workstream is fully integrated at `09ae23f63`; all old leases are
released.  Lower-Lambert investigation is read-only for now.  Let the already
running `/tmp/LowerLambertWPrototype.lean` validation finish and report it in
this branch's registry.  Before any new source edit, request exact files and
declarations in that registry and wait for acknowledgement here.

### `codex/fabius-theorem-polish-20260825`

Remote tip `b3bc48dfd` contains the isolated all-degree
`FabiusUniformSpline.lean` tranche and its registry.  Stop expanding the file
set.  Merge current `main` into the feature branch, record focused build and
direct-consumer status, push the branch, and request integration.  The
coordinator reserves `FabiusUniformSpline.lean` for this tranche until review.

### `codex/fabius-exposition-integration`

Remote tip `c2fa48110` is behind current `main` and changes the same canonical
frontier and primary-exposition artifacts as newer work.  Freeze all those
paths and do not merge the branch wholesale.  Push any unadvertised commits,
then use this branch's registry to enumerate claim-level content that is not
already on `main`; the coordinator will assign the later semantic TeX merge.

### `codex/fabius-theorem-refinements`

Remote tip `1b2cd37dd` has thirteen commits not on the observed campaign base
and touches several hot Lean and documentation paths.  Do not merge or push it
to `main` wholesale.  Preserve and push the feature tip, then update its own
registry with a declaration-by-declaration list of results still absent from
current `main`.  The coordinator will extract reviewed, nonduplicate commits.

**Merge-recovery directive `FABIUS-R001`.** Stop resolving the current merge;
do not stage additional conflict resolutions.  First record these read-only
facts in a scratch note: `git status --short --branch`, `git rev-parse
ORIG_HEAD`, `git rev-parse MERGE_HEAD`, and `git diff --name-only
--diff-filter=U`.  If and only if the worktree was clean immediately before
the merge began, run `git merge --abort`; this returns to the preserved
pre-merge feature tip.  If there was pre-merge dirty work, that fact is
uncertain, or abort fails, leave the worktree untouched and publish the four
facts through this branch's registry after a safe recovery is identified --
never reset, checkout conflicted paths, or choose whole files with
`--ours`/`--theirs`.

After a successful clean abort, push the preserved feature tip if necessary
and make only a registry/status commit.  Do not retry the merge.  The current
candidate extraction is the unique mathematics commit `a95bd1913` (translated
Thue--Morse polynomial coefficient, zero, degree, and leading-coefficient API
in `FabiusQBinomialTaylor.lean`); its README and stale registry/control-plane
edits are excluded.  The coordinator will replay and build that source change
on a fresh branch from current `main`.  All other branch content remains
read-only until inventoried declaration by declaration.

### Claude Fabius branches and any unlisted branch

The observed Claude asymptotic, documentation, theorem, and non-elementarity
tips are ancestors of the campaign base.  Their old leases are closed.  Any
continued work, and any branch not named above, is read-only until it publishes
an exact-path claim in its own registry file and the coordinator acknowledges
it here.

## Collision and integration queue

1. Publish this control-plane checkpoint.
2. Drain the two overlapping `codexbox` builds; record both outcomes without
   treating either dirty-tree result as validation of an immutable SHA.
3. Review and integrate the isolated `FabiusUniformSpline` tranche.
4. Review the checkpointed generalizations commits by dependency layer.
5. Reconcile the canonical frontier in TeX under one owner; rebuild its PDF
   only after the semantic source merge.  Then review the primary exposition
   and walkthrough artifacts.
6. Audit stale exposition/refinement branches claim by claim; never merge
   either wholesale merely to reduce divergence counts.
7. Run focused builds per coherent Lean tranche, followed by one serialized
   aggregate build at an immutable combined SHA.

## Build-token log

At 15:45 PDT the coordinator observed two concurrent jobs on `codexbox`:

- worktree `042c`: `lake build +FabiusFunction.FabiusFullAsymptoticExpansion`;
- worktree `/home/codex/src/Proofs`: `lake env lean /tmp/LowerLambertWPrototype.lean`.

They predate this checkpoint and must be allowed to finish.  Until both exit,
the token is `PAUSED`; no third job may start.  A build owner on the other
physical machine records its independent token in its branch registry.

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
