# Proposal: multi-agent coordination for `Analysis/FabiusFunction`

> **Status:** Draft for review — not current project policy<br>
> **Scope:** `Analysis/FabiusFunction` only<br>
> **Audience:** maintainers, theorem authors, documentation contributors,
> integration agents, and reviewers<br>
> **Feedback requested:** Please respond to the numbered questions in
> [Open decisions](#open-decisions) by following
> [How to give feedback](#how-to-give-feedback).  The integration captain will
> record responses and dispositions in the log below.<br>
> **Provisional decision owner:** Fabius integration captain<br>
> **Target decision point:** After the two-window pilot

This document proposes a lightweight protocol for several AI agents working on
the Fabius formalization at the same time.  It is deliberately a proposal, not
an assertion that the project already follows these rules.  The filename should
remain stable if the proposal is accepted, rejected, or superseded; update the
status and revision history instead.

Related project references:

- [project overview](../README.md);
- [paper-to-theorem coverage](PAPER_COVERAGE.md);
- [asymptotic completion audit](ASYMPTOTIC_COMPLETION_AUDIT.md);
- [aggregate public Lean import](../Lean/FabiusFunction.lean).

## Summary

The proposed operating model is:

1. one integration captain for a Fabius campaign;
2. separate branches and worktrees for independent writers;
3. one active writer for each claimed file and declaration family;
4. immutable upstream SHAs for bounded work waves;
5. one integration funnel with scheduled upstream synchronization;
6. one global Lean-build token for the host;
7. focused validation before one frozen-tree aggregate build; and
8. evidence-rich handoffs and detailed, coherent commits.

The point is not to reduce useful parallelism.  It is to keep mathematical
exploration parallel while serializing the few operations that have global
effects: changing a hot foundational module, staging a shared worktree,
integrating branches, and consuming enough memory to build the development.

## Why this proposal exists

The current campaign has exposed several concrete failure modes.

- `origin/main` can advance more than once during a single merge-and-validation
  cycle.  Merging a symbolic ref after auditing it can therefore merge a
  different commit from the one that was reviewed.
- Repeated main-to-topic and topic-to-main merges create criss-cross history
  and force the same declaration audit to be repeated.  Frequent pushes are
  valuable; frequent synchronization merges are not the same thing.
- Several live branches have touched the same hot clusters: `Basic`,
  `Differential`, probability and weak convergence, arithmetic/parity/two-adic
  results, Laplace modules, Thue--Morse modules, and the README.
- Subagents in one worktree share the source files, index, and `.lake` build
  directory.  A broad stage, format, stash, or merge can absorb another
  worker's unfinished changes even when their assigned mathematics is
  disjoint.
- Git refs and stashes are shared by all worktrees in the repository.  A stash
  ordinal such as `stash@{0}` can change when another actor creates a stash.
- Separate worktrees still share the 14 GiB Windows host, toolchain I/O, and
  memory pressure.  Concurrent activity has coincided with transient
  `.olean`/`.olean.private` read failures, while the host has also approached
  low free memory; both conditions increase the risk of misleading build
  failures or process termination.
- A focused green build can remain valid evidence for one exact SHA while no
  longer proving the state of a branch that has since merged upstream.
- Documentation can name a theorem before its final public name and hypothesis
  boundary have stabilized.

These are coordination problems, not failures of any particular agent.  The
protocol should make the safe path obvious and inexpensive.

## Goals

- Increase useful mathematical parallelism without overwriting peer work.
- Make file, declaration, integration, and validation ownership explicit.
- Detect stale or duplicated theorem ideas before proof engineering begins.
- Respect the Lean import graph when extracting common lemmas.
- Keep source-facing statements distinguishable from stronger library-facing
  corollaries.
- Make every green claim reproducible and tied to an exact commit.
- Keep public documentation synchronized with the theorem API.
- Produce frequent, reviewable, pushed commits without fragmented or
  ping-pong merge history.
- Recover cleanly from interrupted workers, upstream overlap, or transient
  Windows build failures.

## Non-goals

This proposal does not:

- permanently choose the mathematical research priorities;
- replace repository, user, system, or agent instructions;
- authorize destructive Git operations;
- grant implicit write access outside a declared work package;
- require a particular AI implementation or orchestration tool;
- serialize read-only audits that can safely run in parallel;
- treat a focused build as proof that the aggregate development is green;
- require rebasing or force-pushing shared history; or
- make archival TeX or generated PDFs authoritative over their intended source.

## Invariants and trust boundaries

The following rules should hold throughout the pilot.

1. **Unfamiliar dirty changes belong to somebody else until proved otherwise.**
   Do not reset, discard, reformat, stage, stash, pop, or commit them.
2. **One active writer owns a file.**  Read-only auditors may inspect it.  A
   second writer needs an explicit transfer or a split into nonoverlapping
   files.
3. **Declaration ownership matters as well as file ownership.**  Two agents
   should not independently add differently named versions of the same result.
4. **Lower import layers have a larger blast radius.**  Moving or generalizing
   a foundational theorem requires the owner of that layer and its focused
   validation lane.
5. **No hidden trust changes.**  New `sorry`, `admit`, axioms, unsafe shortcuts,
   or weakened source-faithfulness must be reported and reviewed explicitly.
6. **Validation claims are SHA-qualified.**  A command run against another
   commit or before a later merge is historical evidence, not current proof.
7. **Paper-faithful wrappers remain identifiable.**  A stronger all-real or
   generic corollary should not silently replace the statement used to map a
   numbered source theorem.
8. **Derived artifacts follow their sources.**  Edit the TeX or other source,
   regenerate once under an assigned owner, and do not hand-merge binary PDFs.

## Proposed roles

Roles describe responsibilities, not permanent agent identities.  One agent
may hold more than one role when the authority is stated explicitly.  A role
or work-package claim never grants authority beyond the user, repository, or
agent instructions already in force.

### Integration captain

- records the pinned campaign and upstream SHAs;
- assigns and releases ownership claims;
- owns the integration worktree, index, synchronization merges, and
  integration-branch pushes;
- resolves cross-branch semantic conflicts with the relevant module owner;
- owns the global Lean-build token unless it is delegated; and
- publishes the final evidence and remaining uncertainty.

The captain should use a dedicated clean integration worktree.  A dirty `main`
checkout containing unrelated work is not an integration environment.

### Theorem or refactoring worker

- owns exact files and expected declarations for one bounded work package;
- searches current and upstream code for stronger or duplicate results first;
- edits only the owned files;
- reports required focused and downstream build targets; and
- hands off a clean immutable commit on its private branch.

### Documentation and coverage worker

- owns the README/coverage files only during an explicit documentation phase;
- verifies every named declaration against the final Lean source;
- preserves the distinction between source coverage and library strengthening;
- checks local links and generated-artifact provenance; and
- avoids editing a theorem name that is still under active review.

### Read-only auditor

- may inspect any branch, worktree, source, diff, or build output;
- reports overlap, dependency direction, stale work, and validation gaps;
- does not edit, stage, commit, merge, stash, or start an unassigned build.

### Validation owner

- holds the single build token;
- freezes the source tree for the duration of the claimed validation;
- runs the agreed focused-to-aggregate ladder; and
- reports exact commands, SHAs, exit status, warnings, and infrastructure
  failures.

## Work-package contract

Every writing task should start with a claim containing at least:

```text
Objective:
Agent:
Branch:
Worktree:
Campaign HEAD:
Pinned origin/main SHA:
Owned files:
Expected public declarations or documentation:
Read-only dependencies:
Files explicitly excluded:
Expected Git operations already authorized:
Explicitly prohibited operations:
Validation responsibility and requested targets:
Known dependencies on another package:
Lease/checkpoint time:
Escalation condition:
```

The default lease is one bounded work wave.  A claim becomes active only after
the captain acknowledges it with a claim ID.  Thirty to forty-five minutes or
two to four commits is a liveness checkpoint, not an automatic ownership
transfer: renew, release, or revoke the lease explicitly.  An interrupted
worker must release ownership and list all dirty files; the captain may revoke
an inactive claim only after auditing its worktree and recoverable commits.

Directory-wide ownership should be rare.  New isolated subtrees are a natural
exception, but existing Lean and documentation files should normally be named
individually.

## Module ownership and dependency layers

Ownership should follow the import graph.  A useful approximate layering is:

1. **Foundations:** `Arithmetic.lean`, `Basic.lean`, and shared definitions such
   as binary weight or Thue--Morse sign.
2. **Core discrete algebra:** parity, dyadic correctness/closed forms, and
   Thue--Morse prefix/generating/exponential modules.
3. **Probability and approximation:** probability representation, weak
   convergence, measure bridges, step approximants, and uniform splines.
4. **Moments, transforms, and valuations:** normalized/analytic moments,
   Laplace transforms, negative-Laplace modules, denominators, and two-adic
   results.
5. **High-level applications:** inverse-dyadic and q-binomial formulas,
   Legendre/Fourier expansions, saddle asymptotics, paper wrappers, and human
   documentation.

Rules at these boundaries:

- Extract a common helper in the lowest module that can state and prove it
  without an import cycle.
- Land a foundational API commit before refactoring multiple downstream
  consumers when practical.
- A downstream owner may request a lower-layer helper but should not duplicate
  it locally while waiting.
- Generalizing coefficients from `ℚ` to a field or ring deserves a separate
  review: a mathematically stronger theorem can still worsen typeclass
  inference or downstream usability.
- Keep a convenient specialized corollary when the generic theorem is awkward
  for the dominant consumer.
- Aggregate imports, `README.md`, and `PAPER_COVERAGE.md` are hot files owned by
  the captain or one explicitly assigned documentation worker.

The following are currently hot declaration families and should be serialized
until the live branches converge:

- folded-function parity, range, support, and differential facts in `Basic`
  and `Differential`;
- CDF/probability/support facts in `ProbabilityRepresentation` and
  `WeakConvergence`;
- arithmetic, parity, normalized moments, and two-adic valuation APIs;
- real/complex Laplace bridges and negative-Laplace estimates; and
- root imports and human-facing module maps.

## Pinned synchronization windows

### The central rule

**Frequent commits and pushes; periodic synchronization merges.**

At the start of a wave, the captain starts from a committed campaign head and
fetches main into a unique, wave-local ref.  A normal remote-tracking ref and
`FETCH_HEAD` are shared by all worktrees; another fetch can move either between
two shell commands.  A unique destination ref closes that race:

```powershell
$syncRef = "refs/fabius-sync/$([guid]::NewGuid().ToString('N'))"
git fetch origin "refs/heads/main:$syncRef"
$campaignHead = git rev-parse HEAD
$baseMain = git rev-parse $syncRef
$mergeBase = git merge-base $campaignHead $baseMain
git diff --name-status "$mergeBase..$baseMain" -- Analysis/FabiusFunction
git diff --name-status "$mergeBase..$campaignHead" -- Analysis/FabiusFunction
```

All work and audits in the wave refer to `$campaignHead` and `$baseMain`, not
to the moving symbolic name `origin/main`.  If another worktree fetches while
the wave is active, the shared remote-tracking ref may move; the pinned SHA
and unique sync ref do not.  Delete the temporary ref with
`git update-ref -d $syncRef` after the merge is committed and the SHA is
recorded.  Only the captain creates synchronization refs or performs ordinary
remote fetches while the synchronization lock is held.

Do not chase every upstream commit mid-proof or reopen a completed merge merely
because unrelated main work arrived during validation.  Synchronize at the
next window unless the new commit touches an actively owned hot file.

### Cadence

Open a synchronization window:

- at campaign start;
- after two to four coherent commits or roughly 30--45 minutes;
- before a new public API change in a hot foundational module;
- when upstream lands overlapping work in an owned file;
- at the combined integration-handoff/final-validation boundary.

During a synchronization window:

1. freeze the integration worktree and the workers whose immutable commits are
   entering this window, and wait for the active build to finish; unrelated
   worktrees may continue source work outside the build token;
2. ensure the integration tree is clean or coherently checkpointed;
3. fetch once and pin the newly observed main SHA;
4. inspect the upstream path and declaration delta;
5. merge the pinned SHA exactly once;
6. resolve conflicts semantically and audit both parents;
7. run the affected focused targets under the build token;
8. push and broadcast the new campaign and main SHAs; and
9. reassign leases for the next wave.

For a pushed feature or integration branch, prefer an explicit merge of the
pinned SHA.  Prevent Git from auto-committing a clean textual merge before the
semantic audit and detailed message are ready.  Do not rebase or force-push
history others may consume.

```powershell
git merge --no-ff --no-commit $baseMain
# Resolve and audit, run the focused pre-commit gate, then create the detailed
# merge commit before checking ancestry.
git commit -m '<detailed merge subject>' -m '<semantic resolution and validation>'
git merge-base --is-ancestor $baseMain HEAD
if ($LASTEXITCODE -ne 0) { throw "Pinned main is not an ancestor of HEAD" }
git update-ref -d $syncRef
```

The merge commit should record the exact upstream SHA, overlapping APIs,
semantic resolution, and validation.  Only the captain performs upstream
merges on the integration branch.

### Integration funnel

The default flow is:

```text
worker branches -> Fabius integration branch -> authorized PR or handoff
                         ^
                         |
             scheduled authorized main sync
```

Avoid repeatedly merging main into several sibling topics and immediately
merging each topic back into main.  That pattern creates ping-pong topology
without producing additional mathematical review.

The diagram describes data flow, not authority.  Promotion to `main`, direct
push, PR creation, force operations, branch deletion, and worktree deletion
still require whatever authority the user and repository workflow independently
provide.

Before a final claim of currency, distinguish two questions:

1. Was the pinned relevant main SHA merged and validated?
2. Has main since advanced in Fabius paths that affect this work?

An unrelated advancement need not force a ceremonial merge.  Report the drift
and let the next scheduled window absorb it.

## Git and shared-worktree discipline

- Require a distinct branch and worktree for every independent writer during
  the pilot.  The integration worktree is captain-only; read-only auditors may
  inspect it.  Each writer worktree must have its own checked-out branch.
- If the environment temporarily forces several subagents into one worktree,
  they count as one composite writer under a whole-worktree lease.  Exactly one
  of them writes at a time; none performs Git or validation operations, and all
  freeze before the captain builds or commits.
- Inspect `git status` before and after every handoff.  Never assume the files
  in the status belong to one worker.
- Stage exact owned paths, not the entire worktree.
- Do not run repository-wide formatting while other leases are active.
- Do not create new stashes during the pilot.  Preserve unfinished work in a
  clearly named private WIP branch and commit.  Existing stashes are
  captain-managed, read-only until deliberately reconciled, and never
  referenced solely by ordinal.
- Never use destructive reset/checkout to resolve an ambiguous dirty tree.
- Only the captain may remove/prune a campaign worktree or delete a worker
  branch, and only after checking its resolved absolute path, porcelain status,
  pushed/recoverable commits, and integration state.
- Do not normalize line endings or format the repository during a campaign.
  For a suspiciously large Windows diff, inspect `git diff --numstat`,
  `git diff --ignore-space-at-eol`, and `.gitattributes`, and isolate any
  mechanical churn from semantic Lean edits.
- Never resolve a hot Lean module wholesale with `--ours` or `--theirs`.
- Do not amend, rebase, or force-push a commit after another branch has based
  work on it.

Recommended commit sequence for an extraction:

1. reusable theorem in its canonical layer;
2. downstream proof simplifications;
3. additional corollaries;
4. documentation and public-import changes; and
5. a separate synchronization/conflict-resolution commit.

Each commit message should say **why**, **what API changed**, **which duplication
was removed**, and **what validation ran**.  Push after every coherent green
commit.

The workable chronology is: edit; create an unpushed local commit; build that
exact commit; fix it with another private commit or amend it while no consumer
can have observed it; add the final validation evidence to the message or
handoff; then push.  Never amend after another branch may have consumed the
commit.

## Stale-work audit before proving a theorem

Before implementation, search the pinned campaign and main SHAs for:

- the intended declaration name and plausible alternate spellings;
- the conclusion embedded in a stronger theorem;
- generic polynomial/coefficient or measure results that imply it;
- private downstream copies;
- recent commits in the same mathematical family; and
- changed consumers or import direction.

Useful commands include:

```powershell
git log --all -S'<declaration>' --oneline -- Analysis/FabiusFunction
git grep -n '<declaration>' $baseMain -- Analysis/FabiusFunction
git diff --name-status "$mergeBase..$baseMain" -- Analysis/FabiusFunction
git diff --name-status "$mergeBase..$campaignHead" -- Analysis/FabiusFunction
git rev-parse "HEAD:Analysis/FabiusFunction/Lean/FabiusFunction/Basic.lean"
git rev-parse "$baseMain`:Analysis/FabiusFunction/Lean/FabiusFunction/Basic.lean"
```

Pivot rather than duplicate when upstream already contains the result.  Useful
pivots include a genuinely generic theorem, a short compatibility corollary,
consumer refactoring, better discoverability, or removal of obsolete private
machinery.

## Lean build scheduling and validation

### One global build token

At most one logical Lean/Lake/cache job or process tree should run on the host
for this campaign.  An elan wrapper, its toolchain `lake` child, and Lean
children all belong to the same token holder and count as one job.  During the
pilot, only the captain launches builds.  The captain announces the exact
target and frozen campaign state; other Fabius agents may perform read-only
analysis but do not start `lake`, `lean`, cache extraction, or another
compiler.  This project-local protocol cannot preempt unrelated host builds,
so the captain must inspect them and defer when necessary.

Before taking the token on Windows, inspect existing processes and available
memory.  Verify PID, command line, worktree, and start time before considering
termination of an orphan.  Do not start an aggregate build when another Lean
process is active or free physical memory is already low.

Each worktree has its own `.lake` project output, but all builds contend for
the same RAM, toolchain files, antivirus scanning, and disk I/O.  Do not copy
project `.olean` files between worktrees as a substitute for validation.

A small wrapper that implements an atomic host-wide build lease is a useful
follow-up; see [Open decision Q3](#open-decisions).  Until then, captain-only
invocation is the enforceable default.  Never kill an unregistered or merely
suspicious process; only its owner or the captain may terminate an exactly
identified invocation after validating PID, command, start time, and worktree.

### Validation ladder

For a semantic Lean change:

1. `git diff --check` on the owned paths;
2. inspect imports, exact declarations, assumptions, and duplicate names;
3. build the lowest changed module;
4. build direct consumers of its public API;
5. build a meaningful adjacent subsystem target;
6. commit the integration tree, confirm `git status --porcelain` is empty, and
   run exactly one `lake build FabiusFunction` at that immutable commit;
7. inspect added diff lines for new `sorry`, `admit`, `axiom`, or `unsafe`
   declarations, and run `#print axioms` for designated exported theorems when
   the campaign's trust standard requires it; and
8. record the exact HEAD, command, exit status, warnings, and upstream SHA.

Focused pre-commit builds are useful while a worktree is dirty, but they must
be reported as validation of that worktree state rather than of `HEAD`.  A
SHA-qualified final claim requires the slice to be committed and the relevant
focused or aggregate gate to run against that immutable commit.  During a
`--no-commit` merge, the captain may run the focused gate before committing;
the final aggregate gate belongs after the detailed merge commit exists.

Documentation-only changes may replace Lean elaboration with link resolution,
exact declaration-name checks, source/render comparison, and the appropriate
Markdown/TeX validation.  Comments inside Lean files should still receive a
focused build when practical because malformed comments or encoding can break
parsing.

A focused retry can classify a transient aggregate failure, but it does not
retroactively make the aggregate green.  If Lean reports failure to read an
existing `.olean` or `.olean.private`:

1. wait for every competing build to exit;
2. verify the referenced file exists;
3. retry the failed target alone;
4. report both outcomes; and
5. do not launch competing aggregate builds to see which one wins.

Do not invent unsupported Lake flags.  Prefer target granularity and a single
build owner over undocumented parallelism controls.

## Semantic conflict resolution

Resolve Lean conflicts by mathematical relationship, not textual preference.

1. Freeze source editing during integration.
2. Ask the owner of the lowest conflicting layer to classify the changes.
3. Determine whether the declarations are identical, one generalizes another,
   complementary, proof-only, or relocated across an import boundary.
4. Preserve the smallest canonical API that covers real consumers, has the
   appropriate assumptions and import placement, and retains necessary stable
   or paper-facing wrappers.  Check typeclass inference, names, simp attributes,
   and current callers rather than equating logical strength with API quality.
5. Retain a compatibility or paper-facing wrapper only when it has a real
   consumer or documentation role.
6. Compose complementary APIs rather than dropping one silently.
7. Check import direction and cycles.
8. Search for conflict markers and duplicate declaration families.
9. Build the resolved module and at least one downstream consumer.
10. Explain the decision in the merge commit.

For example, an assumption-free structural parity theorem belongs at the
lowest definition layer, while an `IsFabius` compatibility wrapper may remain
downstream.  Likewise, an unrestricted probability identity can coexist with
the restricted theorem that faithfully maps a paper's stated domain.

Generated artifacts follow a different protocol: choose or merge the
authoritative source, regenerate the artifact once, and validate that pair.

## Handoff contract

Every worker handoff should contain:

```text
Branch and worktree:
Campaign HEAD and pinned origin/main SHA:
Ownership released:
Files changed:
Declarations added, generalized, moved, or removed:
Assumptions or imports changed:
Source-facing compatibility retained:
Focused validation and exact outcome:
Adjacent/aggregate validation and exact outcome:
Warnings or infrastructure failures:
Unstaged/untracked/stashed state:
Possible upstream overlap:
Recommended next targets:
Commit and push status:
Remaining uncertainty or follow-up opportunity:
```

The captain independently inspects the diff and status before staging it.
“Build looked green” or “compiled earlier” is not a sufficient handoff.

## Failure and recovery

### Overlap discovered mid-task

Stop writing the shared declaration family.  Keep the work recoverable, compare
the pinned branches, and let the captain decide whether to transfer ownership,
compose the APIs, or pivot the task.

### Upstream advances mid-wave

Continue against the pinned SHA unless an owned hot file changed.  Report the
new tip as drift; do not discard valid proof work or create an immediate merge
for unrelated commits.

### Worker becomes unavailable

The captain records its owned paths and dirty state, interrupts any orphaned
build only after PID verification, and recovers from a private WIP commit or a
fully identified stash.  Ownership is then explicitly reassigned.

### Validation is partial

Commit or hand off only with an honest validation section.  A textual audit,
focused build, adjacent build, and aggregate build are different evidence
levels.  Never upgrade one into another in prose.

### Work becomes redundant

Do not add a synonym merely to preserve effort.  Extract the nonredundant
generalization, refactor consumers through the stronger upstream theorem,
improve documentation, or discard the redundant diff while retaining a clear
audit record.

## Tentative Fabius work plan

This allocation is a starting point for discussion, not a permanent roadmap.
Only three worker lanes should run alongside one captain at a time.

### Wave 0: converge the live branches

1. Create or select a clean dedicated Fabius integration worktree.
2. Record the exact tips and changed-path inventories of `main`, the active
   Codex theorem-refinement branch, the active Claude strengthening branch,
   and any remaining generalization branch.
3. Freeze new edits to `Basic`, `Differential`, `ProbabilityRepresentation`,
   `Parity`, `TwoAdic`, the aggregate import, and README until their live
   variants are semantically compared.
4. Integrate low-layer API changes before leaf refactors and documentation.
5. Run focused builds serially for every conflict cluster, then one aggregate
   build on the frozen integration SHA.
6. Publish the new campaign/base SHAs and release the next ownership leases.

### Wave 1: three independent slices

| Lane | Proposed owned modules | Near-term objective | Coordination dependency |
| --- | --- | --- | --- |
| Discrete algebra | `ThueMorsePrefix`, `ThueMorseGenerating`, `ThueMorseExponential` | Extract the affine sharp-degree power-sum theorem, choose the right coefficient generality, and refactor centered/translated proofs | Treat freshly changed arithmetic/parity modules as read-only until Wave 0 lands |
| Analytic transforms | `LaplaceTransform`, `LaplaceMoments`, `NegativeLaplace*` | Remove private real/complex bridge duplication and expose useful positivity/derivative corollaries | Consume the canonical core coercion/range API selected in Wave 0 |
| Order and regularity | `Regularity`, `Monotonicity`, `Convexity`, `BoundedDerivatives`, flatness modules (pending Wave-0 integration from the active strengthening branch) | Review and integrate the existing strict-order, Lipschitz, convexity, and sharp-flatness work | Must not independently edit `Basic`/`Differential`; request core changes from the captain |

The captain owns probability/core conflicts, the aggregate import, and build
scheduling during this wave.  With four total slots, a read-only documentation
auditor alternates with one worker lane rather than running as a fifth
participant.  Actual README/coverage edits wait until theorem names stabilize.

### Wave 2: probability and approximation

- Consolidate endpoint, support, CDF, and measure-convergence APIs.
- Strengthen quantitative finite-approximation bounds where the current
  convergence theorems expose the necessary estimates.
- Consume the generic Thue--Morse affine theorem in uniform-spline code only
  if its coefficient type genuinely supports the real-valued consumer.
- Remove private recurrences or affine proofs after, not before, the canonical
  theorem is integrated.

### Wave 3: arithmetic and formula consumers

- Re-audit normalized moments, denominators, and two-adic formulas after their
  recent upstream strengthening.
- Review inverse-dyadic and q-binomial consumers for translation-specific
  duplication that a common coefficient theorem can remove.
- Keep Legendre/Fourier work in a separate ownership lane from probability
  modules unless a precise theorem transfer is agreed.

### Documentation pass

One owner updates `README.md`, `PAPER_COVERAGE.md`, module docstrings, and any
human-readable synthesis after the public declarations land.  Source owners
provide exact theorem names and hypothesis summaries.  Regenerate each derived
PDF once from the final source and verify links and rendering.

## Pilot rollout and success measures

Pilot the protocol for two synchronization windows with:

- one captain and clean integration worktree;
- two independent theorem/refactoring packages;
- one read-only stale-work or documentation audit;
- one serialized validation lane; and
- captain-owned integration commits.

Measure:

- zero overwritten or accidentally staged peer changes;
- zero unexplained files in commits;
- zero overlapping top-level build invocations recorded by the captain;
- every handoff names exact SHA and validation outcome;
- fewer duplicate theorem declarations and private helper copies;
- fewer merge conflicts in hot modules;
- no main/topic ping-pong inside a work wave;
- public documentation updated in the same campaign; and
- useful theorem/refactoring output per bounded package.

After two windows, review whether the protocol's ceremony saved more time than
it cost.

## Alternatives and tradeoffs

- **Shared versus separate worktrees:** a shared worktree makes integration
  immediate but shares the index, dirty state, and validation inputs.  The
  pilot therefore requires separate writer worktrees.  A later revision may
  consider a whole-worktree single-writer lease where tooling cannot provide
  another worktree.
- **Exact-file versus module-family ownership:** exact files reduce ambiguity;
  families reduce handoff overhead.  Start exact and expand only when the
  import boundary is stable.
- **Captain-only versus worker commits:** captain-only commits protect a shared
  worktree.  In separate private worktrees, workers can safely commit and push
  coherent slices for the captain to integrate.
- **One global versus several focused-build lanes:** multiple `.lake`
  directories do not create more physical RAM.  The current host favors one
  global token; a larger builder could revisit this.
- **Tracked versus ephemeral status ledger:** a tracked ledger is durable but
  conflict-prone; agent messaging is current but ephemeral.  A review issue or
  small generated dashboard may be a better long-term ledger.

## Open decisions

Please respond using the IDs below so feedback is easy to reconcile.

| ID | Decision | Proposed default | Feedback requested |
| --- | --- | --- | --- |
| Q1 | Ownership granularity | Exact files and declaration families | When is a module-family claim safer? |
| Q2 | Commit authority | Private-worktree owners commit/push immutable handoffs; captain integrates | Should all Fabius commits instead be captain-owned during the pilot? |
| Q3 | Lean build token | Captain-only invocation; later add an atomic wrapper | Should the future token be a lock directory, named mutex, wrapper script, or external queue? |
| Q4 | Active-status ledger | Kickoff/handoff messages during the pilot | Would a GitHub issue, checked-in ledger, or generated dashboard be more reliable? |
| Q5 | Synchronization cadence | 30--45 minutes or two to four commits, plus overlap events | Is this too frequent or too coarse for long Lean proofs? |
| Q6 | Integration topology | Worker topics → one integration branch → authorized PR/handoff | Is a permanent Fabius integration branch desirable? |
| Q7 | Validation before handoff | Hygiene plus focused target; adjacent/aggregate owned by captain | Which public-API changes require an adjacent build by the worker? |
| Q8 | Hot-file ownership | Captain or explicitly assigned single writer | Should aggregate imports and README always be captain-owned? |
| Q9 | Stash policy | No new stashes during the pilot; captain inventories existing ones | Are there emergencies for which a base-qualified patch is insufficient? |
| Q10 | Adoption scope | Pilot in `Analysis/FabiusFunction` only | Which results would justify a repository-wide convention? |

## How to give feedback

Preferred feedback channels, in order:

1. inline comments on the review pull request once one exists;
2. a repository discussion or issue linked from this document;
3. a focused commit on a review branch; or
4. a handoff message that the captain records below.

Please distinguish:

- blocking concerns from optional refinements;
- observed failures from hypothetical risks;
- disagreement with the proposed default from disagreement with the goal; and
- a simpler enforceable alternative from a rule that merely sounds safer.

Especially useful feedback includes counterexamples, commands that work across
Windows worktrees, and evidence from other multi-agent formalization campaigns.

## Feedback and disposition log

| ID | Reviewer | Feedback | Disposition | Follow-up |
| --- | --- | --- | --- | --- |
| — | — | No feedback recorded yet | Pending review | Link the review PR or issue when created |

## Revision and decision history

| Date | Status | Change | Decision reference |
| --- | --- | --- | --- |
| 2026-08-24 | Draft for review | Initial proposal based on the first concurrent Fabius strengthening campaign | TBD |
