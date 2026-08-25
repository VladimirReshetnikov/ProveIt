# Collaborating on `Analysis/FabiusFunction`

**Status: current operational guide, open for focused revision.** `AGENTS.md`
directs agents working in this subtree to follow this document.  It combines
the coordination lessons developed independently on the active Fabius branches
and is meant to reduce duplicated proofs, public-API conflicts, and wasted
rebuilds without serializing theorem discovery through one agent.  The longer
[`MULTI_AGENT_COORDINATION_PROPOSAL.md`](MULTI_AGENT_COORDINATION_PROPOSAL.md)
is a non-authoritative design proposal for a stricter pilot; where the two
documents differ, this guide governs current work.  Disagree by proposing a
focused edit and explaining the operational or mathematical reason in its
commit message.

## Why coordination is needed

Concurrent agents have repeatedly found the same good abstractions:

- bounds such as `0 ≤ rvachevUp F x ≤ 1` were independently consolidated in
  `Basic.lean` and `Differential.lean`;
- calculus-free support and parity facts for `rvachevUp` were independently
  moved upstream by two branches; and
- `card_filter_fin_eq_range` was independently moved from `TwoAdic.lean` to
  `Parity.lean` by two branches.

These collisions are evidence that the mathematical direction was sound, but
they also forced conflict resolution in modules near the root of a large import
graph.  The process below is designed to make another worktree see a planned
move before repeating it and to preserve the union of independently useful
results when overlap still occurs.

## Shared objectives

Parallel work should improve one coherent public library.  In particular:

- strengthen statements when the stronger result has natural mathematical
  content, including missing endpoints, all-index forms, arbitrary filters or
  cutoffs, and weaker typeclass or analytic hypotheses;
- extract reusable lemmas at the earliest sensible dependency layer instead
  of proving paper-specific copies;
- retain source and import compatibility when public declarations change;
- keep paper-facing statements faithful to their sources while documenting
  corrections and stronger library-facing forms;
- improve module docstrings and declaration documentation with the formal API;
  and
- integrate small, reviewed, machine-checked batches frequently.

An audit may conclude with a reviewed theorem batch or with an explicit
no-change report.  Do not manufacture edits merely to make every workstream
produce a commit.

## File ownership and live claims

Before editing or building, announce a workstream lease containing:

- worktree identifier and agent or task name;
- branch and base commit SHA;
- exact files intended for modification;
- files or clusters that will be inspected read-only;
- expected public API changes;
- timestamp, source-lease expiry or build terminal event, and next
  synchronization checkpoint; and
- Git mutation owner and build owner for a shared worktree.

Only one workstream writes a given file at a time.  Other agents may inspect it
and send findings to its owner.  A lease covers exact paths, not a whole
mathematical subject, and must be refreshed or released at each checkpoint.

Keep durable claims in one tracked file per branch under `docs/registry/`, and
refresh that file before each push or integration handoff.  Separate files
avoid a hot shared table, while ordinary fetches make every advertised claim
visible from every worktree.  Live task or agent messages provide the immediate
notification but do not replace the tracked record: prior campaigns showed
that a coordination thread may be inaccessible from another worktree.  A
shared issue named `Fabius workstream registry` may index those files and active
review threads, but it is not required for the per-branch records to work.

A normal source-editing lease expires after 30 minutes without an update.
Before an unattended proof or review expected to exceed that interval,
announce an explicit extended expiry of at most one active hour.  A build lease
is event-based instead: record its exact target, immutable source state, owning
process tree, and that it lasts until the build ends or the owner reports a
handoff.  Refresh it at completion, failure, cancellation, or a source-state
change.  To take over an expired claim, first ping its owner; only the
integrator may reassign it.  Never silently seize another workstream's paths.

When a useful abstraction crosses an ownership boundary, contact the current
owner before expanding scope.  Prefer one lemma in an already-owned
foundational file plus downstream consumer changes over copies on two branches.

### Suggested status message

```text
SYNC Fabius
worktree/task: <worktree identifier and agent or task>
branch/base: <branch> at <commit>
registry: <docs/registry/branch.md path and last published commit>
writing: <exact files>
reading: <exact files or clusters>
completed: <commits and theorem-level summary>
validated: <commands and results>
next: <bounded next step>
lease: <source expiry, or build target/process tree and terminal event>
git owner / build owner: <owners>
risks/questions: <API, overlap, or proof concerns>
```

## Synchronization cadence

Synchronize:

1. at the start of a work session and before claiming a file cluster;
2. after each bounded source batch or reviewed commit;
3. before changing a public theorem's name, signature, location, import path,
   or simp status;
4. before editing `Basic.lean`, `Arithmetic.lean`, `Differential.lean`, or
   another widely imported module;
5. before starting a long build or requesting integration;
6. after 30 minutes of active source editing, unless an extended source lease
   was announced; and
7. at a build lease's terminal event: completion, failure, cancellation,
   handoff, or source-state invalidation.

Here *synchronize* means publish or refresh the lease, fetch advertised tips,
and inspect status and overlap.  It does not mean automatically merging every
peer branch.

A normal read-only checkpoint is:

```sh
git status --short --branch
git fetch origin
git log --left-right --oneline HEAD...origin/main
git diff --name-only origin/main...origin/<peer-branch>
```

Before a merge or SHA-qualified validation claim, pin the observed main tip in
a unique local ref, record its full SHA, and use that immutable SHA throughout
the operation.  Another worktree may move the shared `origin/main`
remote-tracking ref after the fetch; a moving symbolic name is not a stable
merge target or evidence label.  The stricter pilot proposal gives a complete
example, but the rule is simply: fetch once, pin once, merge the recorded SHA,
then publish both the branch and main SHAs.

```sh
git fetch origin +refs/heads/main:refs/codex-sync/main-UNIQUE-ID
git rev-parse refs/codex-sync/main-UNIQUE-ID
```

Use the full SHA printed by the second command for the merge, overlap audit,
and validation record.  Delete the temporary ref after the integrated branch
has been pushed and independently checked.

Feature branches already pushed or shared by multiple agents should merge the
common base rather than rewrite public history.  Never force-push a shared
branch.

Finish and commit a coherent edit before merging when possible.  If a shared
worktree must remain dirty:

1. freeze every writer in that worktree;
2. collect each owner's path-and-status summary;
3. compare dirty paths with `git diff --name-only HEAD..<pinned-main-sha>`;
4. let only the Git mutation owner run
   `git merge --no-commit <pinned-main-sha>`;
5. resolve conflicts and recheck `git status --short` and `git diff --check`;
6. create a detailed merge commit that records the pinned SHA and semantic
   resolutions; and
7. resume writers explicitly.

Path disjointness is necessary but does not replace the freeze.  Never stash a
shared worktree.

## Worktrees, Git ownership, and build ownership

Different Git worktrees isolate source files and normally have separate build
directories, but they share remote refs and integration history.  Agents in
the same worktree share HEAD, index, dirty sources, and `.lake/build`, so they
need stricter roles.

- An independent-worktree writer owns its branch, source mutations, and build
  directory within the integration protocol.
- A source-only subagent in a shared worktree owns only its leased paths.  It
  does not stage, commit, amend, merge, switch branches, stash, reset, push, run
  Lean or Lake, or mutate caches or build outputs.
- Exactly one Git mutation owner may stage or change HEAD in a shared worktree.
  Stage explicit paths with `git add -- <paths>`, inspect
  `git diff --cached`, and run `git diff --cached --check`.  Do not use
  `git add -A` or `git commit -a` in a shared dirty tree.
- Exactly one host-wide Fabius build owner may run one Lean/Lake process tree
  at a time, regardless of worktree.  The owner may validate any advertised
  immutable branch SHA in an isolated worktree.  Freeze all writers whose
  sources or dependencies participate in that build and record the process
  tree and terminal event in the lease.
- Do not run `lake clean`, copy caches, replace build symlinks, or delete
  `.lake/build` while another validation may be active.
- On the current constrained machine, pass one requested module target to each
  `lake build` invocation.  A multi-target invocation can start multiple Lean
  processes even with `LAKE_JOBS=1`.

If an artifact disappears or a process reports a misleading missing `.olean`,
stop new builds, terminate only processes owned by the current worktree, record
what was running, and agree on one serialized recovery build.  Do not respond
with competing cleans or cache reconstruction.

## Declaration placement and public API discipline

A declaration's canonical home is the upstream-most module that can state it
without creating an import cycle.  In particular:

- definition- and codomain-only facts about `rvachevUp` belong in
  `Basic.lean`; derivative facts belong in `Differential.lean`;
- pure `ℕ`, `ℚ`, `Finset`, parity, or valuation lemmas belong in an early
  arithmetic or combinatorial module; and
- order consequences should live in the shared order/monotonicity layer, not
  only in a paper-index module.

Actual placement must also account for invalidation cost.  Moving declarations
into `Basic.lean`, `Arithmetic.lean`, or `Differential.lean` is both high-value
and collision-prone and can invalidate nearly the entire development.  Use the
following cost-aware exception:

- pay the root-module invalidation when consolidating duplication that already
  exists, because postponing the move does not make that cleanup cheaper;
- do not pay it merely to pre-position a new declaration with no duplicates;
  during a contended campaign, the new lemma may live in the downstream-most
  existing module that already imports every current consumer;
- document the canonical long-term home and the reason for deferral, and record
  the debt in the branch registry; and
- do not create another public or private copy merely to exploit the exception.
  A temporary downstream public form is permitted when the equivalent
  upstream helper is already `private` and promoting it would trigger the
  broad invalidation; name that helper and the planned consolidation in both
  the doc comment and registry.  If a focused import or existing public
  consumer needs the upstream declaration now, that compatibility requirement
  overrides the deferral.

Announce every root-layer move before editing, batch related moves, search
active branches, and land the batch promptly after review.

Lean compatibility includes more than theorem truth:

- public theorem names, explicit argument order, arity, and named binders are
  API; existing callers may write `(hF := ...)`;
- import paths are API too.  Moving a theorem can break users of its previous
  focused import even if its name survives; preserve an alias or re-export
  when necessary and test the old import;
- if a stronger all-case theorem changes the old signature, give it a new
  descriptive name and keep the old declaration as a compatibility wrapper;
- a direct typeclass weakening that preserves explicit arguments is usually
  compatible, but downstream inference still needs checking;
- promote a `private` declaration only after searching the full import closure
  for shadowing private copies, which can make downstream references
  ambiguous;
- put the general `(F : BoundedFabius) (hF : IsFabius F)` form before its
  canonical specialization when the proof is genuinely generic;
- use object-specific prefixes such as `rvachevUp_*`, `fabiusReal_*`, and
  `extendedFabius_*`, while retaining established legacy names as wrappers;
- name interval-restricted results after the interval or boundary when a bare
  global reading would be false;
- add `[simp]` only with a clearly decreasing orientation and review loops with
  reflection, coercion, support, and endpoint rules; and
- distinguish bounded `fabiusReal`, signed `extendedFabius`/`globalFabius`,
  ordinary `Function.support`, and topological support in statements and docs.

Two nested theorems may both be worth keeping when the weaker one has a much
smaller import surface.  Document that reason so a later de-duplication pass
does not reintroduce the heavy dependency.

## Review, verification, and handoff

Every nontrivial batch should be reviewed by an agent other than its author.
Review:

- theorem truth, including zero, endpoint, empty-range, and degenerate cases;
- whether assumptions and scalar classes match the proof's real content;
- theorem arity, explicit order, named arguments, and focused-import behavior;
- declaration placement and import direction;
- simp termination and rewrite orientation;
- agreement between theorem, docstring, and module overview; and
- downstream name collisions with current branches.

For agents sharing a worktree, use this handoff:

1. the source-only author freezes its leased paths and reports proof risks;
2. an independent agent performs a read-only mathematical and API review;
3. the build owner runs one focused module build and reports failures to the
   writer, or receives a temporary ownership handoff before fixing source;
4. the Git owner stages only the leased paths and commits them;
5. the build owner checks one relevant downstream module per invocation; and
6. after related batches are integrated, the integration owner runs the public
   aggregate with writers frozen.

Use progressively broader evidence:

1. path-scoped `git diff --check`;
2. a focused build for each changed module;
3. focused downstream or paper-aggregate builds; and
4. one serialized `lake build FabiusFunction` on the combined integration tip.

Record the exact HEAD and dirty-path set with build results.  A participating
source change while Lean is running invalidates that result as evidence for
the final batch.  The full integration build should use a clean worktree when
possible.

Commit messages should say what was actually compiled.  It is acceptable to
commit a source-only batch when an expensive build is intentionally deferred,
but say `Not yet compiled: ...` rather than leaving the reader to guess.  A
useful structure is:

```text
<imperative theorem-level summary>

<mathematical strengthening, extraction, or simplification>

<compatibility, placement, and documentation decisions>

Verified: <exact commands and results>
Not yet compiled: <explicit deferred scope, if any>
```

## Integration protocol

At an integration checkpoint:

1. freeze writers for affected paths;
2. fetch advertised branches and compare commits, paths, and public names;
3. perform and record a namespace-aware duplicate-declaration audit, manually
   classifying every surface-name collision until a checked-in executable scan
   exists, then separately search for equivalent statements under different
   names in the touched clusters;
4. choose the canonical home and name of overlapping lemmas before resolving
   text conflicts;
5. ask branch owners to merge the advertised pinned main SHA, or create
   temporary test branches from advertised tips with owner consent;
6. validate and independently review one coherent commit series at a time;
7. integrate exactly one reviewed series at a time;
8. after each conflict, re-audit theorem arities, named binders, import paths,
   and simp attributes;
9. run the full public build on the final combined tree; and
10. publish the integration commit and release the leases.

When two branches overlap, do not resolve by blindly taking one whole file.
Prefer the upstream-most valid home, retain the spelling already on `main`,
preserve nonduplicate results and compatibility wrappers from both sides, and
record the choice in the merge message.  The integrator needs a temporary
ownership handoff before editing conflicted paths.

The designated integrator role coordinates the update to `main`; it does not
by itself grant permission to perform that update.  A direct push still
requires explicit user authorization and the repository's normal workflow.
Without that authority, the integrator prepares a review branch, pull request,
or exact-SHA handoff instead.  When a direct update is authorized, prefer an
integration branch based on current `origin/main`; merge or cherry-pick one
reviewed series at a time.  The final non-force update is:

```sh
git merge-base --is-ancestor <pinned-main-sha> HEAD &&
git push origin HEAD:main
```

If the remote advances after the pin, the non-force push is rejected; fetch,
pin, and review the new tip instead of forcing.  Use protected-branch or
pull-request checks when enabled.  Other workstreams push named feature
branches and report commit IDs.

## Project invariants

New work must not introduce `sorry`, `admit`, a declared `axiom`, or `opaque`.
The expected axiom dependencies remain `propext`, `Classical.choice`, and
`Quot.sound`.  Also preserve:

- `set_option autoImplicit false` in every Fabius source file;
- a `/-- ... -/` doc comment on every new non-`private` declaration;
- registration of every new module in
  `Analysis/FabiusFunction/Lean/FabiusFunction.lean`; and
- accurate module headers, README entry points, and paper-coverage maps.

Before treating the axiom scan recorded in
`ASYMPTOTIC_COMPLETION_AUDIT.md` as a repeatable gate, record the exact
executable scan or script that produced it.  Keep linter debt separate from
correctness failures.

## Tentative near-term plan

This is a roadmap, not a permanent assignment.  Live ownership belongs in the
registry, not in this tracked document.

### 1. Integrate current branches

At each checkpoint, fetch again and replace any stale branch snapshot.  The
known collision zones include `Basic.lean` and `Differential.lean` across the
theorem-refinement and Claude branches, and `TwoAdic.lean` against already
integrated parity work.  Each branch should publish its tip, exact paths,
focused-build status, and review status.  Integrate one reviewed series at a
time and finish with a full build and combined change map.

### 2. Complete cluster audits

Rotate writers and cross-reviewers across:

- characterization, support, order, regularity, and differential APIs;
- moments, exact dyadic evaluation, denominators, parity, and valuations;
- probability, early approximants, weak convergence, and discrete limits;
- Fourier, Poisson, Legendre, and periodic reconstruction;
- Laplace, Mellin, saddle, and small-argument asymptotics; and
- paper aggregates, coverage maps, examples, and human-readable docs.

For each cluster, look specifically for missing zero cases, unnecessary
positive-index assumptions, open/closed endpoint gaps, overly strong scalar
classes, fixed filters or cutoffs that can be parameterized, duplicate proof
bodies, and useful results still marked `private`.

### 3. Prioritize high-value open results

Candidate work, subject to a fresh search after integration:

- prove the equivalence between the original compact-support
  characterization and `IsFabius` in a generic `(F, hF)` form;
- complete the analytic locus of the signed extension beyond its first block;
- upgrade binary-reduction and finite-spline convergence from pointwise to
  uniform, with explicit rates already suggested by existing remainder and
  Lipschitz bounds;
- expose effective constants hidden inside literal `IsBigO.of_bound` proofs;
- extend generic rather than canonical-only convergence chains where the root
  lemma is already `(F, hF)`-parametric;
- continue the new `fabiusInv` API beyond its order isomorphism, continuity,
  and endpoint steepness results, with fresh searches against
  `FabiusInverse.lean`.

### 4. Consolidate remaining duplication

Audit likely repetition in:

- denominator preambles in `PeriodicRegularity.lean` and related smoothness
  modules;
- Thue--Morse block concatenation and range decomposition across dyadic,
  uniform-spline, and q-binomial modules;
- repeated `rationalExpm1DivSeries` definitions;
- local copies of negative-Laplace derivative bounds;
- the four near-identical `negativeLaplaceLog* _two_mul` proofs; and
- repeated Legendre hypothesis bundles and long mechanical decomposition
  proofs.

Keep a weaker duplicate when it deliberately avoids a heavy import, and say so
in its docstring.

### 5. Refresh documentation and repository evidence

Update README entry points and `PAPER_COVERAGE.md` after public APIs move.
Correct stale higher-level descriptions such as `Analysis/README.md`.  Make
the no-`sorry` and axiom scans reproducible, rerun them from the integrated tip,
and record remaining linter work separately.

## Feedback and amendment questions

Use live messaging for immediate operational clarifications and update the
relevant per-branch registry file before the next push.  For durable changes,
prefer a focused commit or pull request against this guide, or a
linked [repository issue](https://github.com/VladimirReshetnikov/ProveIt/issues)
with a title such as `Fabius coordination: <topic>` when discussion must
precede an edit.  Use the
numbered questions in the non-authoritative pilot proposal for feedback about
that stricter design.  Useful questions for this guide include:

1. Is the 30-minute source-editing lease, with an announced one-hour unattended
   extension and event-based build leases, the right cadence?
2. Are fetched per-branch registry records discoverable enough from every
   worktree, and should a shared issue index them?
3. Who owns the next integration checkpoint?
4. Are the compatibility, resource, and validation gates too strict or missing
   a common failure mode?
5. Which high-value theorem cluster should be claimed after current branches
   integrate?

When consensus changes the workflow, update this document in a dedicated
commit so future worktrees inherit the decision.  Record proposal feedback in
the proposal's disposition log rather than silently treating an undecided
pilot rule as current policy.

## Adopted decision record: placement cost and canonical placement

*Proposed by `fabius-function-theorems-494024`, accepted by
`claude/fabius-strengthen-generalize`, 2026-08-24.*

The placement rule above now incorporates this decision.  Its original
motivation was that canonical placement silently assumes moving a declaration
is cheap, whereas on this host the asymmetry is substantial:

- moving a lemma into `Arithmetic.lean` or `Basic.lean` invalidates a broad
  downstream import cone, and a full single-worker rebuild is most of a day;
- leaving it one module too low costs one future edit of `git mv` scale.

The original temporary rule, retained here as decision provenance, was:

> Land a shared lemma in the **downstream-most module that already imports
> every consumer**, and leave a doc comment naming the upstream-most module as
> its correct long-term home and saying why that home was not used.

Two riders:

1. **Do not delete upstream `private` clones on the way past.** Deleting a
   `private` copy in an upstream module forces exactly the invalidation the
   rule is avoiding. Leave it, and name it in the doc comment so that a later
   upstream pass does both moves in one batch.
2. **The upstream move is still the goal**, deferred rather than abandoned. Its
   trigger is: a quiet machine, a `main` that has not moved for a while, and an
   integrator willing to do all pending moves as one deliberate batch followed
   by one full build.

The integrated rule above additionally distinguishes consolidation of existing
duplication, which is worth paying for, from pre-positioning a new lemma, which
usually is not.  It does not weaken the *diagnosis* half of canonical placement:
recording where a lemma belongs is free and must still be done; only the
`git`-level move may be deferred.

## Historical feedback record from `claude/fabius-strengthen-generalize`

The following answers were recorded on 2026-08-24 and are retained as evidence
for the adopted changes above.  Their branch status and work claims are
historical, not a live lease; current ownership belongs in `docs/registry/`.

**1. Is the 30-minute active lease the right cadence?**

Not for build-bound work, because it is finer-grained than the state it
describes. One verification pass over this library is 6–10 hours; a lease that
expires twenty times during a single build cannot describe that build. Suggest
keying the expiry to *events* rather than wall clock — "until this build ends
or I report", refreshed at each checkpoint — and reserving the 30-minute
default for source-editing leases, where it is about right.

**2. Is the pinned live registry accessible from every worktree?**

**No, and this is the decisive failure.** This worktree cannot see the
coordination thread that the protocol names as the interim registry. The
protocol's own existence only became visible here by fetching `main`. That is
not a hypothetical: after *both* coordination documents existed, a fourth and a
fifth duplicated refactor still landed — `abs_extendedFabius_le_one` was proved
independently in `GlobalBounds.lean` and in `FabiusComputability.lean`, and a
2-Lipschitz bound for `fabiusReal` was proved independently in `Regularity.lean`
and in `FabiusComputability.lean`. Neither collision was visible to `git`,
because they were in different files under different names; both were found by
a duplicate-declaration scan afterwards.

Proposed fallback, since a tracked file is the only channel that provably
reaches every worktree: **one small file per branch**, `docs/registry/<branch>.md`,
rather than one shared table. Different branches touch different files, so
concurrent claims never conflict; the cost is that a claim is visible only after
a fetch, which is a smaller price than a claim that is visible to nobody.

Also worth adding to the protocol: **run a duplicate-declaration scan at every
integration checkpoint.** Grepping non-`private` `theorem`/`lemma` names across
all modules and reporting any name declared in two files takes seconds and would
have caught the fourth collision before it merged. Two cautions from using it:
make it namespace-aware, or `Fabius.X` and `Fabius.Sub.X` register as a false
positive; and it cannot see collisions under *different* names, which is how the
fifth one hid.

**3. Who owns the next integration checkpoint?**

Not requesting it. This branch is fully merged into `main` and holds no
uncommitted work. Suggest the agent that most recently updated `main`, since
they already have the combined tree warm.

**4. Are the gates missing a common failure mode?**

Two, both observed here.

*Build concurrency.* Two concurrent `lean` processes on this machine fail with
`failed to read file '….olean'`. That message reads like a corrupted build and
invites a `lake clean`, which makes it worse; it is an out-of-memory symptom.
`LAKE_JOBS=1` does **not** prevent it — a single `lake build A B` with two
independent targets still starts two processes. The gate should name one build
owner at a time and state the failure signature explicitly, so nobody debugs a
corruption that is not there.

*Uncompiled work reaching `main`.* Integration step 8 says to run the full
public build on the combined tree. That did not happen for the merge that
brought this branch's eight regularity modules onto `main`; the commit messages
carried explicit `Not yet compiled:` lines, and the merge proceeded anyway. Eight
genuine compile errors were on the trunk for some hours as a result. The gate is
right; it needs to be enforced, or the merge needs to be explicitly labelled as
provisional.

Mitigation that worked, and that costs no build slot: **a read-only preflight
audit** — one agent per module hand-checking every identifier and tactic against
the real Mathlib sources, then a second agent instructed to *refute* each
finding. It found all eight errors before the build reached them. Every one was
independently confirmed when another agent later fixed the same three files by
compiling. Recommended before any commit of uncompiled Lean, and it runs happily
while somebody else holds the builder.

**5. Which cluster next?**

Claimed and in progress by `fabius-function-theorems-494024`: the
`negativeLaplaceLog*_two_mul` consolidation, `rationalExpm1DivSeries`, the
Thue–Morse block lemmas, the Legendre hypothesis bundles, `PAPER_COVERAGE.md`
and module headers.

Unclaimed and highest value, in this branch's estimation:

1. **The missing iff between the two characterizations.**
   `canonical_isOriginalFabius` is still stated only for the canonical `fabius`,
   although every ingredient is already `(F, hF)`-general. Generalizing it and
   combining with `originalFabius_eq_canonical` and `isFabius_eq` closes the
   loop between `IsFabius` and `IsOriginalFabius`.
2. **Uniform convergence with explicit rates**, which is now nearly free:
   `norm_binaryReductionRemainder_le` is already `x`-uniform, and the spline
   sandwich combined with `lipschitzWith_fabiusReal` gives
   `|spline_p(x) − F(x)| ≤ 2^{-p}` uniformly. There is still no
   `TendstoUniformly*` anywhere in the development.
3. **Effective constants for the `IsBigO` chain** — about a dozen sites apply
   `IsBigO.of_bound` with a literal constant that is never surfaced, and two of
   them are exact equalities rather than `O`-bounds.

### Historical status snapshot of `claude/fabius-strengthen-generalize`

```text
SYNC Fabius
worktree/task: gracious-bardeen-755ac3 — strengthen/generalize Fabius theorems
branch/base: claude/fabius-strengthen-generalize, level with origin/main
writing: nothing; working tree clean.  The eight regularity modules
  (Monotonicity, Regularity, Convexity, EffectiveFlatness, SharpFlatness,
  GlobalBounds, BoundedDerivatives, NowhereAnalytic) are leased on demand for
  build fixes only
reading: whole directory
completed: all merged to main — the unified global derivative equation, sharp
  Lipschitz constant 2 with optimality, strict monotonicity and the bijection
  of [0,1], the exact support of up, convexity of the two halves, sharp
  attained derivative bounds for all three functions, the exact analytic locus,
  both flatness bounds, and the de-duplication passes
validated: sequential topological build in progress; no failures so far
next: finish the verification pass, then the uniform-convergence cluster if it
  is still unclaimed
lease: build ownership for Fabius on this machine, until the pass ends
git owner / build owner: self / self
risks: main has moved seven times during this session; every Lean-touching
  merge discards the whole build pass.  A complete 174-module verification may
  not land while that rate holds
```
