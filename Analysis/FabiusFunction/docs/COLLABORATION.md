# Fabius collaboration and coordination proposal

This document proposes a lightweight protocol for people and AI agents working
on `Analysis/FabiusFunction` in parallel worktrees.  It is intended to reduce
duplicate proofs, conflicting API changes, and avoidable integration failures
without centralizing all theorem discovery in one workstream.

This is a proposal, not immutable policy.  Please suggest changes through the
same coordination channel used to announce work, or in a small dedicated
commit that explains the operational problem being solved.

## Shared objectives

Parallel work should improve one coherent public library.  In particular:

- strengthen statements when the stronger result has a natural mathematical
  meaning, including missing endpoints, all-index forms, arbitrary filters,
  and weaker typeclass or analytic hypotheses;
- extract reusable lemmas at the earliest sensible dependency layer instead
  of proving paper-specific copies;
- retain source compatibility when public declarations are generalized;
- keep the paper-facing statements faithful to their sources while clearly
  documenting corrections and stronger library-facing forms;
- improve module docstrings and declaration documentation together with the
  formal API; and
- integrate small, reviewed, machine-checked batches frequently.

## One writer per file

Before editing, announce a workstream with:

- the worktree identifier and agent or task name;
- the branch and current base commit;
- the theorem cluster and exact files intended for modification;
- files that will be inspected read-only;
- expected public API changes; and
- the claim timestamp, expiry, and next synchronization checkpoint.

Only one workstream should write a given file at a time.  Related agents may
read the same files and propose changes, but they should send findings to the
declared writer instead of making competing edits.  A claim is scoped to the
listed files, not to an entire mathematical subject.  Refresh or release it at
each synchronization checkpoint so that abandoned work does not remain
implicitly reserved.

Treat file claims as short leases in one canonical live registry, keyed by
worktree, agent or task, branch, base SHA, exact paths, timestamp, and expiry.
The first integration owner should create and pin a shared issue or task named
`Fabius workstream registry`; until that exists, the shared coordination thread
where this protocol is announced is the registry.  Do not use a tracked file
as the authoritative live registry: branches see tracked updates only after
fetching or merging.  The integrator acknowledges new claims.  To take over an
expired claim, first ping its owner; only the integrator may reassign it, and
no workstream should silently seize the paths.  Until the team chooses a
different default, a lease expires 30 minutes after its last active-work
status update.  Before an unattended proof or review expected to exceed that
interval, announce an explicit extended expiry of at most one active hour; the
lease remains valid until that time without a heartbeat.

When a new opportunity crosses an existing boundary, contact the current file
owner before expanding the scope.  Prefer a new lemma in an already-owned
foundational file plus a consumer change in the downstream file over copying
the result into both branches.

### Suggested status message

```text
SYNC Fabius
worktree/task: <worktree identifier and agent or task>
branch/base: <branch> at <commit>
writing: <exact files>
reading: <exact files or clusters>
completed: <commits and theorem-level summary>
validated: <commands and results>
next: <bounded next step>
lease: <timestamp and expiry>
risks/questions: <API, overlap, or proof concerns>
```

## Synchronization cadence

Use both event-driven and periodic synchronization.

Synchronize:

1. before claiming a new file cluster;
2. after each coherent, focused-build-clean commit;
3. before changing a public theorem's signature, name, location, or simp
   status;
4. before starting a full aggregate build;
5. before requesting integration; and
6. after one bounded source batch or 30 minutes of active work, whichever
   comes first, even if the current proof is incomplete.

Here *synchronize* means publish or refresh the lease, fetch advertised tips,
and review status and overlap.  It does not mean merging all branches.  A long
unattended proof may report immediately before and after its run only when its
lease announced the extended expiry above.  No claimed file should block
another ready workstream for more than one active hour without an owner update.

A normal feature-branch checkpoint is:

```sh
git status --short --branch
git fetch origin
git log --left-right --oneline HEAD...origin/main
git diff --name-only origin/main...origin/<peer-branch>
```

Finish and commit the current coherent edit before merging when possible.  If
the worktree must remain dirty, freeze every writer in that worktree, collect a
path-and-status summary from each owner, and verify that the incoming commit
does not touch any dirty path.  Use `git diff --name-only HEAD..origin/main`
for the incoming paths; the three-dot peer-branch command above answers a
different question.  Never stash a shared worktree.  Only the Git mutation
owner should perform the merge, then recheck `git status --short` and
`git diff --check` before explicitly resuming writers.  Merge the shared base
rather than rewriting public history:

```sh
git merge --no-edit origin/main
```

For branches already pushed or used by more than one agent, prefer merge
commits over rebases.  Never force-push a shared branch.  Push each reviewed
batch so that other worktrees can inspect its actual commit rather than a
verbal summary.

Synchronization does not mean automatically merging every peer branch.  First
inspect its changed paths and public declarations.  Integrate peer work through
the designated integration branch or through `main`, unless both owners agree
that a direct feature-to-feature merge is the clearest dependency.

## Worktrees, source edits, and build caches

Different Git worktrees isolate source files, but their agents still share
remote branches and integration history.  Agents in the *same* worktree share
both uncommitted source and `.lake/build`; they require stricter coordination.

Distinguish two collaboration levels:

- an independent-worktree writer owns its branch, source mutations, and build
  directory within the shared integration protocol; and
- a source-only subagent in a shared worktree owns only its declared files.
  The parent workstream names exactly one Git mutation owner and one build
  owner for that worktree.

- Do not edit, reset, clean, stash, or switch another workstream's files.
- Never use destructive Git commands to resolve an ownership mistake.
- Source-only subagents do not stage, commit, merge, switch branches, or run
  any Lean, Lake, cache, or other build-output-mutating command.
- Only the Git mutation owner may stage or change HEAD.  Stage explicit owned
  paths with `git add -- <paths>`, inspect `git diff --cached`, and run
  `git diff --cached --check` before committing.  Do not use `git add -A`,
  `git commit -a`, amend, stash, reset, switch, merge, or push from another
  shared-worktree agent.
- Within one worktree, serialize Lean and Lake invocations.  Concurrent builds
  can replace or remove the same `.olean` output while another process reads
  it.
- Do not run `lake clean`, copy caches, replace build symlinks, or delete
  `.lake/build` while any agent may be validating.
- A source-only subagent should report proof-risk locations and leave all Lean
  execution to the worktree's build owner.
- Separate worktrees may build concurrently when their build directories are
  genuinely separate, but each worktree should still have one build owner.

If a build artifact unexpectedly disappears, stop new builds, terminate only
the invocations owned by the current worktree, record the commands that were
running, and agree on one serialized recovery build.  Do not respond with
competing cleans or cache reconstruction.

## Public API discipline

Lean source compatibility includes more than theorem truth.

- Public theorem names, explicit argument order, theorem arity, and named
  binders are API.  Existing calls may use arguments such as `(hF := ...)`.
- When removing an assumption or covering a missing boundary case changes the
  old signature, add a clearly named stronger theorem and keep the old theorem
  as a short compatibility wrapper.
- A direct typeclass weakening that preserves the explicit arguments is
  normally compatible, but still check downstream inference.
- Put generic algebra, arithmetic, combinatorics, and filter lemmas in the
  earliest appropriate module.  Avoid making reusable facts depend on a late
  paper aggregate.
- Search for an existing result before adding one.  When two branches discover
  the same abstraction, select one canonical declaration and refactor both
  consumers through it.
- Add `[simp]` only when the rule has a clear decreasing orientation.  Review
  possible loops with existing reflection, coercion, support, and endpoint
  rules.
- State endpoint conventions and necessary side conditions in docstrings.
  Distinguish the bounded `fabiusReal`, signed `extendedFabius`/`globalFabius`,
  ordinary `Function.support`, and topological support explicitly.
- Import paths are also API.  Moving a theorem can break a user of the old
  focused import even when its name and signature survive.  Preserve an alias
  or re-export in the old module when necessary, and include the old focused
  import in downstream validation.

## Review and verification gates

Every nontrivial batch should be reviewed by an agent other than its author.
The reviewer should check:

- mathematical truth, including zero, endpoint, empty-range, and degenerate
  index cases;
- whether hypotheses and typeclasses are minimal for the proof's real content;
- public signature and named-argument compatibility;
- declaration placement and import direction;
- simp termination and rewrite orientation;
- agreement between the theorem, its docstring, and the module overview; and
- likely downstream name collisions with other active branches.

Use progressively broader validation:

1. `git diff --check` on the scoped changes;
2. `lake build FabiusFunction.<ChangedModule> ...` for the changed modules;
3. focused downstream or paper-aggregate builds; and
4. one serialized `lake build FabiusFunction` on the integration result.

Freeze every source writer whose files or dependencies participate in a build.
Record the exact HEAD and dirty-path set with the result; if a participating
source changes while Lean is running, the result is not evidence for the final
batch.  Focused checks in a dirty shared tree should use path-scoped
`git diff --check` and report the dirty inputs.  The full integration build
should run with all writers frozen and preferably with a clean worktree.

Do not claim that a broad aggregate is valid from focused builds alone.  On
the other hand, do not make every source-only experiment wait for a full build;
run the broad gate once the coherent batches have been integrated.

For agents sharing a worktree, use this handoff pipeline:

1. the source-only author freezes its scoped files and reports proof risks;
2. an independent agent performs a read-only mathematical and API review;
3. the build owner runs focused Lean checks and reports failures to the writer,
   or receives an explicit temporary file-ownership handoff before making
   elaboration fixes;
4. the Git mutation owner stages only the declared paths and commits them;
5. the build owner runs the relevant downstream aggregate; and
6. after the related batches are combined, the integration owner runs the
   full public build.

Commit messages should record the mathematical change, compatibility choices,
documentation work, and exact validation performed.  A useful structure is:

```text
<imperative theorem-level summary>

<what was strengthened, generalized, extracted, or simplified>

<compatibility, placement, and documentation decisions>

<focused and aggregate validation evidence>
```

## Integration protocol

At an integration checkpoint:

1. freeze writers for the affected files;
2. fetch all advertised branches and compare their commits and changed paths;
3. choose the canonical version of overlapping lemmas before resolving textual
   conflicts;
4. ask each branch owner to merge `origin/main`, or create a temporary
   integration/test branch from the advertised tip rather than mutating a
   stale shared feature branch without consent;
5. run focused validation and independent review on each batch;
6. integrate exactly one coherent commit or commit series at a time;
7. run the full `FabiusFunction` build after the final combined tree; and
8. publish the resulting integration commit and release the file claims.

Only the explicitly designated integrator should update `main`.  Prefer a
temporary integration branch based on the current `origin/main`, then merge or
cherry-pick one reviewed series at a time.  The final non-force update is:

```sh
git fetch origin
git merge-base --is-ancestor origin/main HEAD && git push origin HEAD:main
```

If the remote advances, the non-force push is rejected; fetch and review the
new tip instead of forcing.  Use the repository's protected-branch or pull
request checks when enabled.  Everyone else should push named feature branches
and report their commit IDs.

When two branches overlap substantially, do not resolve the conflict by
blindly taking one file.  Compare declarations theorem by theorem, preserve
the union of nonduplicate results, retain compatibility wrappers from both
sides, and ask the file owners to review the combined diff.  The integrator
must receive an explicit temporary ownership handoff for every conflicted path
before editing it.  After resolving each conflict, explicitly re-audit theorem
arities, named binders, and simp attributes; these API details are easy to lose
in a textually clean merge.

## Tentative near-term plan

The following is a proposed sequence, not a permanent assignment.

### 1. Integrate the current parallel branches

The following ephemeral snapshot was verified after `git fetch origin` and
must be updated or removed at every integration checkpoint:

| Verified | Branch and tip | Divergence from `origin/main` | Status or known overlap |
| --- | --- | --- | --- |
| 2026-08-24 | `origin/main` at `4bd083335f` | -- | Current integration base |
| 2026-08-24 | `origin/codex/fabius-generalizations` at `8f47e17ef3` | 2 behind, 0 ahead | Integrated into current `main`; sync with `main` before further work |
| 2026-08-24 | `origin/codex/fabius-theorem-refinements` at `5c528f929c` | 3 behind, 7 ahead | Active; overlaps `Basic.lean` and `Differential.lean` with the Claude branch |
| 2026-08-24 | `origin/claude/fabius-strengthen-generalize` at `cf7b12ba19` | 9 behind, 8 ahead | Active; overlaps `Basic.lean`, `Differential.lean`, and integrated `TwoAdic.lean` work |

Each branch should publish its current file scope, focused-build status, and
review status.  Appoint one integration owner.  Each branch owner should merge
the latest `origin/main`, or the integrator should create a temporary test
branch from the advertised tip with the owner's consent.  Then integrate the
branches one at a time while preserving all nonduplicate APIs.  Finish with a
full build and a short combined change map.  This dated list is only a snapshot;
update or remove entries as branches land.

### 2. Complete cluster-by-cluster API audits

Use separate writers, with cross-reviewers rotated between clusters:

- foundational characterization, support, order, and differential APIs;
- moments, exact dyadic evaluation, denominators, parity, and valuations;
- probability, early approximants, weak convergence, and discrete limits;
- Fourier, Poisson, Legendre, and periodic reconstruction;
- Laplace, Mellin, saddle, and small-argument asymptotics; and
- paper aggregates, coverage maps, examples, and human-readable documentation.

For each cluster, explicitly search for missing zero cases, unnecessarily
positive indices, closed versus open endpoint gaps, overly strong scalar
classes, fixed filters or cutoffs that can be parameterized, and repeated
proof bodies that deserve a shared lemma.

A completed audit may be a reviewed theorem batch or an explicit no-change
report.  Do not manufacture edits merely to make every cluster produce a
commit.

### 3. Consolidate cross-cutting APIs

After the local audits land, run a dedicated pass for duplicate declarations,
import cycles, naming consistency, compatibility wrappers that can now share a
core theorem, and public results stranded as `private`.  Update the README and
paper-coverage map when the recommended entry points change.  Also correct
stale higher-level descriptions such as `Analysis/README.md` when they no
longer reflect the proved Fabius library.

### 4. Re-run repository-level evidence

Build the public aggregate from the integrated tip.  Before citing the
no-`sorry` and axiom audit in `ASYMPTOTIC_COMPLETION_AUDIT.md` as a repeatable
gate, add the exact executable scan or script that produced it; then rerun and
record the command and result.  Record remaining linter debt separately from
correctness failures.  This is the point to decide whether another discovery
round has enough expected value to justify new parallel branches.

## Feedback requested

Please comment in the coordination channel or propose a small edit addressing
one or more of these questions:

1. Is 30 minutes the right maximum interval between synchronization reports?
2. Is the proposed pinned live registry accessible enough from every worktree,
   and what fallback should be used when it is not?
3. Which branch and person or agent should own the next integration checkpoint?
4. Are the compatibility and validation gates too strict or missing a common
   failure mode?
5. Which theorem cluster should be prioritized after the current branches are
   integrated?

When consensus changes the workflow, update this document in a dedicated
commit so future worktrees inherit the decision.
