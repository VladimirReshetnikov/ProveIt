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

Before editing, announce a short workstream lease containing:

- worktree identifier and agent or task name;
- branch and base commit SHA;
- exact files intended for modification;
- files or clusters that will be inspected read-only;
- expected public API changes;
- timestamp, expiry, and next synchronization checkpoint; and
- Git mutation owner and build owner for a shared worktree.

Only one workstream writes a given file at a time.  Other agents may inspect it
and send findings to its owner.  A lease covers exact paths, not a whole
mathematical subject, and must be refreshed or released at each checkpoint.

Keep claims in one canonical live registry rather than a tracked claims table:
branches see tracked changes only after fetching.  The first integration owner
should create and pin a shared issue or task named `Fabius workstream registry`;
until then, the coordination thread in which this protocol is announced is the
registry.  The integrator acknowledges new claims.

A normal active-work lease expires after 30 minutes without an update.  Before
an unattended proof or review expected to exceed that interval, announce an
explicit extended expiry of at most one active hour.  To take over an expired
claim, first ping its owner; only the integrator may reassign it.  Never silently
seize another workstream's paths.

When a useful abstraction crosses an ownership boundary, contact the current
owner before expanding scope.  Prefer one lemma in an already-owned
foundational file plus downstream consumer changes over copies on two branches.

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
5. before starting a long build or requesting integration; and
6. after 30 minutes of active work, unless an extended lease was announced.

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
- Exactly one build owner runs Lean or Lake in a worktree.  Freeze all writers
  whose sources or dependencies participate in the build.
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

A declaration should live in the upstream-most module that can state it
without creating an import cycle.  In particular:

- definition- and codomain-only facts about `rvachevUp` belong in
  `Basic.lean`; derivative facts belong in `Differential.lean`;
- pure `ℕ`, `ℚ`, `Finset`, parity, or valuation lemmas belong in an early
  arithmetic or combinatorial module; and
- order consequences should live in the shared order/monotonicity layer, not
  only in a paper-index module.

Moving declarations into `Basic.lean`, `Arithmetic.lean`, or
`Differential.lean` is both high-value and collision-prone.  Announce it before
editing, batch related moves, search active branches, and land the batch
promptly after review.

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
3. choose the canonical home and name of overlapping lemmas before resolving
   text conflicts;
4. ask branch owners to merge the advertised pinned main SHA, or create
   temporary test branches from advertised tips with owner consent;
5. validate and independently review one coherent commit series at a time;
6. integrate exactly one reviewed series at a time;
7. after each conflict, re-audit theorem arities, named binders, import paths,
   and simp attributes;
8. run the full public build on the final combined tree; and
9. publish the integration commit and release the leases.

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
  lemma is already `(F, hF)`-parametric; and
- study the inverse of `fabiusReal` on `[0,1]`, including its endpoint
  regularity consequences from factorial flatness.

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

Use the live registry for immediate operational clarifications.  For durable
changes, prefer a focused commit or pull request against this guide, or a
linked [repository issue](https://github.com/VladimirReshetnikov/ProveIt/issues)
with a title such as `Fabius coordination: <topic>` when discussion must
precede an edit.  Use the
numbered questions in the non-authoritative pilot proposal for feedback about
that stricter design.  Useful questions for this guide include:

1. Is the 30-minute active lease, with an announced one-hour unattended
   extension, the right cadence?
2. Is the pinned live registry accessible from every worktree, and what
   fallback should be used when it is not?
3. Who owns the next integration checkpoint?
4. Are the compatibility, resource, and validation gates too strict or missing
   a common failure mode?
5. Which high-value theorem cluster should be claimed after current branches
   integrate?

When consensus changes the workflow, update this document in a dedicated
commit so future worktrees inherit the decision.  Record proposal feedback in
the proposal's disposition log rather than silently treating an undecided
pilot rule as current policy.
