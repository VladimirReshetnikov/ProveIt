# Fabius campaign coordinator board

This is the canonical repository-visible control plane for concurrent work in
`Analysis/FabiusFunction`.  Only the designated coordinator edits this file.
Every worker reads it from the fetched `origin/main` before writing, merging,
building, or pushing.  Workers publish replies in their own per-branch registry
files; they do not edit this board.

## Checkpoint 2026-08-25 21:19 PDT

```text
observed main before this directive: a515f57abf854e3ce86b312e0ca3e6e64354003c
coordinator branch: codex/fabius-coordinator-20260825
integration mode: feature branches -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (IDLE after coarse eighth-order reference-tail validation)
codexbox TeX/PDF owner: unassigned
  (IDLE; no active documentation agent)
EVO Lean/Lake owner: unassigned
  (IDLE after shifted-prefix validation)
documentation owner: unassigned
  (all canonical documents frozen pending a new exact-path claim and assignment)
next poll: after the next advertised source checkpoint
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
2. Lean/Lake/cache-mutating compilation remains serialized to one assigned
   process per physical host.  Workers without a host Lean/Lake grant may edit
   and commit unvalidated work, but launch no such process; label those commits
   and registry reports `Not yet validated`.  A board-assigned document owner
   may run one sequential LaTeX/PDF tool stream on codexbox without consuming
   its Lean token, and that stream may coexist with the one assigned Lean
   build.  No document owner or TeX/PDF stream is assigned now.  Do not launch
   parallel TeX passes or terminate another process.
3. The following remain serialized and require an explicit board grant:
   `AGENTS.md`, `README.md`, `docs/COLLABORATION.md`,
   `docs/MULTI_AGENT_COORDINATION_PROPOSAL.md`, `docs/PAPER_COVERAGE.md`,
   `docs/AUDIT_FINDINGS.md`, this board, the root aggregate
   `Lean/FabiusFunction.lean`, and every primary-exposition, walkthrough, or
   canonical-frontier TeX/PDF path.  Any path marked hot, frozen, or
   single-owner below is also unavailable to ordinary claims.  The historical
   exposition and successor frontier gates are recorded below, but no document
   source or PDF phase is currently open.  The prior standing lease is
   released; all canonical document paths are frozen until a new exact-path
   claim is assigned.  The canonical frontier PDF remains single-owner
   whenever a future document owner is assigned.  Host Lean/Lake ownership is
   tracked separately from any future lightweight document lane.
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

Registry checkpoint `db4ef7a31` is accepted as the sole advertised successor
request for the canonical frontier.  The live branch tree itself is not an
acceptable integration base: it is 195 main commits behind the reviewed
checkpoint, contains the obsolete six-part/172-page document pair, and a
read-only merge conflicts in exactly the frontier README, TeX, and PDF.  Do not
merge that stale tree, select either PDF side, or resolve those conflicts.

The workstream must preserve its pushed historical branch, then create a fresh
continuation branch named `codex/fabius-frontier-successor-20260825` from the
coordinator checkpoint carrying this directive.  The pinned input blobs are:

- frontier README `be3865b4b7fabbf09f3af9ce96f7e72098c0cb08`;
- frontier TeX `b284a5e4b7eaef66cf8c38637484b7ac109e945a`;
- inherited, mismatched and frozen PDF
  `0cd676c1d8d1f590acadd813ad42669c8faa5aba`.

**Source-phase grant.**  On that fresh base, this successor owns only the
frontier TeX and its existing branch registry for one checkpoint.  Apply
exactly the three advertised prose hunks around TeX lines 7317--7333: qualify
the blanket direct-corollary introduction, mark `dyadicweb:eq:D-error` as
frontier-dependent on the unformalized shifted-spline estimate, and qualify the
closing blanket paragraph.  Change no formula, theorem, label or reference
*target*, citation, environment, layout token, README, PDF, Lean file, primary
document, or other path.  The single literal
`\eqref{dyadicweb:eq:shifted-spline-bound-local}` in the advertised middle
hunk is explicitly authorized and is expected to increase the reference-token
count by one; it is not a contract violation.  Correct the registry's stale
fetched-main/HEAD fields and state
explicitly that this is a separate successor task with no primary scope.
Commit and push the TeX plus own-registry source checkpoint, then stop for an
independent source audit.

No TeX/PDF/build token is granted.  The canonical PDF remains frozen.  Only
after that exact source checkpoint passes review may the board separately
grant one host token for exactly three sequential `pdflatex` passes and the
post-render inspection.  The eventual render must rebuild the PDF; it must
never reuse or conflict-resolve the old binary.

Historical inputs remain preserved on the old branch:

- `docs/non-formalized-research-frontiers/README.md`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.pdf`

The preserved 172-page rewrite source is `8142ccb19`; its registry handoff is
`8a53bd10a`.  Those bytes are evidence only, not the successor source base.

The successor complied on fresh base `f556a126e`: source commit `7bbd84752`
changes exactly the three advertised TeX prose hunks plus its new own registry,
and registry tip `ff6787ecf` freezes the source while reporting the now-resolved
single-`\eqref` ambiguity.  Its TeX blob is `6812dbf9caeab2c02fe92288f0524fa52256325b`
with SHA-256 `0AE36755EA52945E5032EF9005EA89CB59AAFA91EB36A1AC770FF2F0B53C63AB`.
Independent review passes: the exact paths/base/blobs and three prose hunks are
correct; all 986 labels are unique, every expanded reference and citation
resolves, all 1201 environments are balanced, and `git diff --check` is green.
The single added `\eqref` is the intended resolved dependency pointer.

**Three-pass PDF grant.**  This branch now holds the sole codexbox document
token.  First merge this coordinator checkpoint into the clean pushed feature
branch and verify that the TeX blob remains exactly `6812dbf9c`.  In
`Analysis/FabiusFunction/docs/non-formalized-research-frontiers`, run exactly
three sequential invocations of:

```text
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
  -jobname=non-formalized-research-frontiers_successor_7bbd84752 \
  non-formalized-research-frontiers.tex
```

Run no fourth pass, other TeX compiler, `latexmk`, Lean, or Lake, and make no
source edit during this grant.  The third pass must have: all three exits 0;
settled references/citations; zero undefined, rerun, changed-label,
multiply-defined, fatal, or LaTeX-error diagnostics; and zero overfull
horizontal or vertical boxes.  Then use only read-only `pdfinfo`, `pdffonts`,
`pdftotext`, and `pdftoppm` inspection.  Require embedded fonts, no rendered
`??`, and inspect the changed corollary paragraph, the page-184 table/footer,
and the page-10 opener.

If every gate passes, replace the canonical frontier PDF with the exact settled
third-pass output and commit/push only that PDF plus the successor registry;
the already-frozen TeX commit remains unchanged.  If any gate fails, do not
install a PDF or improvise a fourth pass/source repair: preserve the sidecar,
report exact diagnostics in the registry, push, and stop.  Never push `main`.

**Standing single-owner amendment.**  At the user's request, the preceding
per-hunk and exactly-three-pass restrictions are historical gates for
checkpoint `7bbd84752`/`daa9cb19f`, not the future operating model.  This is
now the only active documentation agent and holds a standing lease for exactly:

- `docs/non-formalized-research-frontiers/README.md`;
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`;
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.pdf`;
- `docs/registry/codex-fabius-frontier-successor-20260825.md`.

Within those four paths it may choose and sequence bounded semantic-status,
human-readable-counterpart, organization, cross-reference, and layout work;
edit locally; commit and push feature checkpoints; and run the sequential
`pdflatex` passes plus read-only PDF/text/font/raster inspections needed to
settle a matching artifact, without requesting a new board acknowledgment for
each hunk or pass.  Advertise each bounded tranche in the own registry before
editing so source agents can see what is happening, but coordinator silence is
not a blocker.  It may update the frontier README and install a source-matched
canonical PDF when its own documented source/static/render gates pass.

This standing lease does not extend to a primary exposition, walkthrough,
campaign-wide Markdown/control-plane file, Lean source, or `main`.  It may not
run Lean/Lake, overlap multiple TeX/PDF processes, use force, or push `main`.
Its single sequential TeX/PDF stream may coexist with the one board-assigned
codexbox Lean/Lake build; neither lane may multiply itself.  On a failed
render, it may diagnose and repair its owned source and rerun as needed rather
than awaiting a micro-grant, but it must preserve/report rejected artifacts and
never install a mismatched PDF.  Release the standing lease explicitly in the
own registry when the frontier workstream is complete or paused.

The current human-readable backlog includes the eight newly validated
discrete-limit declarations, the complete complex Fourier zero locus, the
rational half-q root locus, and the uncorrected-Wikipedia non-equivalence
theorem.  The owner may disposition these in coherent frontier tranches under
the standing lease; it need not fold them into the already-built three-hunk
checkpoint.

The three-hunk checkpoint is now fully accepted and integrated by coordinator
merge `192c423bb`.  Source lineage `7bbd84752` and artifact commit `daa9cb19f`
produce TeX blob `6812dbf9c` and matching PDF blob `d2dd17022`, SHA-256
`225F8E17F9F8512DFCFBD9491AD5D2CA612537B66F1571DFA6F115FA76D904B8`.
The canonical artifact is 1,479,271 bytes, A4, and 188 pages.  Three independent
audits accept the ancestry/path scope, three-pass registry evidence, all 45
embedded/subsetted fonts, zero rendered `??` or out-of-bounds text, and clean
raster inspection of pages 1, 10, 83, 86, 95, and 184--188.  The accepted
source/PDF pair is now the base for the standing frontier lease; the owner may
continue future tranches without relinquishing that lease.

**Standing-lease release.**  The user reports that no documentation agents
remain active.  The successor branch's standing frontier lease and codexbox
TeX/PDF lane are therefore released; the accepted source/PDF pair above
remains the canonical frozen base, but the branch no longer owns or may edit
those paths merely by virtue of its historical work.  A future documentation
worker must first advertise an exact-path claim and receive a new board
assignment.  Once assigned, the relaxed single-owner operating model above
may be reused: no per-hunk micro-grants are required, and its one sequential
LaTeX stream may coexist with one host Lean build.

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

Exact feature tip `c41a52283` published four additional source units:

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

`GlobalExtension.lean` also has a doc-comment-only terminology edit.  Three
independent static reviews found no theorem, API, placement, duplicate,
dependency, import, or scope blocker.  The coordinator merged exactly
`c41a52283`, rather than the moving branch tip, at immutable integration merge
`04d619814`.  All eight focused targets and both minimal paper facades then
passed serially with `LAKE_JOBS=1`:

- `+FabiusFunction.DyadicAnalytic` (2772 jobs);
- `+FabiusFunction.GlobalExtension` (2765 jobs);
- `+FabiusFunction.GlobalDyadic` (2785 jobs);
- `+FabiusFunction.OriginalPaperSupplement` (3210 jobs);
- `+FabiusFunction.BoseFinitePartIntegral` (3268 jobs);
- `+FabiusFunction.PeriodicMean` (3269 jobs);
- `+FabiusFunction.PeriodicRegularity` (3295 jobs);
- `+FabiusFunction.PeriodicSmooth` (3297 jobs);
- `+FabiusFunction.Paper05442` (3417 jobs); and
- `+FabiusFunction.PaperFabiusAsymptotic` (3957 jobs).

Every invocation exited 0.  The seven source-path leases are released, and the
three corresponding proposal-era entries in `AUDIT_FINDINGS.md` are closed in
place.

Four later, mutually disjoint source units are now independently reviewed,
integrated by exact commit, and compiled without merging the moving feature
history:

- `d2df7eaa7`, private support-localization consolidation in
  `AnalyticMoments.lean`, integrated as `f975de00f`;
- `64a95d363`, the complete complex zero loci for `complexSinc`, the Fourier
  product, and the Rvachev transform in `FourierProduct.lean`, integrated as
  `f62058b96`;
- `a987b3bb9`, the rational finite-q-Pochhammer and half-q polynomial root
  loci in `HalfQBinomial.lean`, integrated as `29729991e`; and
- `45b4816c0`, the theorem that exponentiating the literal uncorrected
  Wikipedia logarithmic expression is not asymptotically equivalent to a
  bounded Fabius solution, integrated as `6f98e4804`.

All four exact parent blobs matched the current-main preimages.  Independent
proof/API reviews found no theorem, filter, sign, domain, import, duplicate,
attribute, consumer, or public-signature blocker.  The serialized builds listed
below all exit 0.  These four source paths are released.  Their human-readable
counterparts join the later frontier-document backlog and must not expand the
currently granted three-hunk source checkpoint.

Registry tip `9cbbbda1a` now advertises an ordinary one-file follow-up in
`PeriodicSmooth.lean`: `[simp]` bridges
`forwardDerivativeQuotientPolynomial_one`, `_two`, and `_three`, plus
`negativeLaplaceForwardTermDeriv_two`, `_three`, and `_four`.  No source is
committed at that registry snapshot.  Source commit `c5f0bb3a3` subsequently
implements exactly those six declarations.  Independent review accepts the
recurrence algebra, signs, derivative-index mapping, unconditional domains,
simp directions, placement, imports, and duplicate scan; main had the exact
parent preimage.

The coordinator integrated the exact source as `af3132a31`.  Its first focused
build exposed two proof-elaboration defects: polynomial normalization did not
close the second quotient identity, and a dependent rewrite failed at index
three.  It supplies no validation evidence.  Repair `8d269396a` proves the
three small polynomial identities by extensional evaluation and cleans the
bridge tactics, changing no public statement or attribute.  The retry of
`+FabiusFunction.PeriodicSmooth` completes 3297 jobs, exit 0, with no warnings.
The `PeriodicSmooth.lean` lease is released.

The branch next froze exact source commit `b27fc5259`, extending the
Reshetnikov oddness result to every natural index.  Two independent reviews
accept the zero and positive cases, the deliberate non-extension of the
valuation conjunct at zero, imports, API, and compatibility proof of
`theorem_nine_all`.  The coordinator integrated it as `6d15d9116`; serialized
builds of `+FabiusFunction.Paper06487Supplement` (3243 jobs) and
`+FabiusFunction.Paper06487` (3244 jobs) both exit 0.  The path is released and
the corresponding `AUDIT_FINDINGS.md` entry is closed.

Private-only source commit `6f8c8c046` then deletes the dead 22-line
`integral_unitInterval_max_sub_mul_pow` helper from `FabiusUniformSpline.lean`.
Two independent audits verify zero callers, identical public declaration
lists, and continued use of every retained import/helper.  The coordinator
integrated it as `b16fc9a6d`; `+FabiusFunction.FabiusUniformSpline` completes
3415 jobs, exit 0.  That path is released and its audit finding is closed.

Registry claim `1686a1a06` advertised an ordinary two-source tranche in
`Differential.lean` and `Existence.lean`: public generic bridge
`rvachevUp_hasDerivAt_of_fabiusReal_hasDerivAt`, specialization of the
unchanged `rvachev_hasDerivAt`, and replacement of the duplicate candidate
three-case proof while preserving `rvachevCandidate_hasDerivAt` and
`rvachevCandidate_even` exactly.  Independent preflight finds the hypotheses
sufficient in the negative, zero, and positive cases, the candidate use
noncircular, both current-main preimages unchanged, and no competing claim or
implementation.  Exact source commit `dbb7ace60` was integrated as
`12fda28c7`.  The first `+FabiusFunction.Differential` attempt exposed only a
generic-tail simplification mismatch at `rvachevUp F 1` and supplies no
validation evidence.  Statement-preserving repair `15563b7dd` makes the two
fold-endpoint zeros explicit.  At the repaired tree, separate serialized
builds of `+FabiusFunction.Differential` (2653 jobs) and
`+FabiusFunction.Existence` (2783 jobs) both exited 0 without warnings.  No
import, old public header, document, audit ledger, facade, or root path changed.
The two source leases and codexbox token are released.

Exact source commit `1b0792b2b5773879b94c07742b4e181c6afbe0d8`
adds only
`norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_all` in
`FabiusDiscreteLimitComplexShift.lean`.  Three independent audits verify the
vacuous empty-sum degree-zero case, truncated exponent, positive-degree
delegation, unchanged old APIs/imports/callers, exact current-main preimage,
and absence of a competing implementation.  The coordinator integrated it as
`f6cb1efd8`.  Separate serialized builds of
`+FabiusFunction.FabiusDiscreteLimitComplexShift` (1873 jobs) and its direct
consumer `+FabiusFunction.FabiusComplexShiftSpline` (3417 jobs) both exited 0
without warnings.  This implements only the first part of the broader audit
proposal; the audit entry remains open.  The source lease and codexbox token
are released.

The branch registry incorrectly spells that source SHA as nonexistent
`1b0792b2b22ed51b28404cc42175befb45313668` in three places.  Correct it in the
next own-registry checkpoint to the full SHA above; this bookkeeping defect
does not affect the integrated source or compiler evidence.

Registry claim `86c3c746b` advertises the disjoint downstream continuation in
`FabiusComplexShiftSpline.lean`: two all-degree/all-real translation bounds and
three all-real real/rational/Gaussian-rational convergence wrappers, with all
existing restricted APIs preserved.  The ordinary source-only claim is
nonoverlapping and may proceed in that one Lean file plus the own registry,
without Lean/Lake.  Keep the stronger `exp ‖δ‖ - 1` estimate open and touch no
audit ledger, document, facade, root, or other path.  An immutable source
checkpoint still requires exact review before any validation token.

Exact source commit `3c2d1e926` implements that continuation and was integrated
as `19ee18206`.  Two independent reviews accept all five declarations, including
the degree-zero, zero-coordinate, and nonpositive-real cases; exact source
blobs, imports, attributes, existing public headers, and the upstream all-degree
dependency were checked.  The old restricted theorem bodies remain
byte-preserved rather than being rewritten as literal wrappers, which is a
nonblocking compatibility choice.  A serialized
`+FabiusFunction.FabiusComplexShiftSpline` build completed 3417 jobs and exited
0 without warnings at the integrated tree.  This downstream continuation is
accepted, and its source lease and codexbox token are released.  The stronger
`exp ‖δ‖ - 1` frontier estimate remains open.

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

Source commit `0f7d53e8c` is a separate two-path unit in
`FabiusDiscreteLimitToeplitz.lean` and
`FabiusDiscreteLimitIntegration.lean`.  It adds eight finite-depth value,
nonconstancy, shift-difference, and outer-index-one comparison results.  Two
independent reviews found the mathematics, domains, indexing, `RCLike`
transport, API, placement, imports, duplicates, and scope green.  The
coordinator cherry-picked only that source as `de8707b44`.

The first Toeplitz build exposed proof elaboration defects in the two concrete
natural-floor evaluations and final generic-field normalization; it grants no
validation evidence.  Repair `8e09c4d98` supplies explicit `Nat.floor_eq_iff`
witnesses and `push_cast` before `ring`, changing no public statement.  At that
repaired immutable tree, serialized `LAKE_JOBS=1` builds of
`+FabiusFunction.FabiusDiscreteLimitToeplitz` (3320 jobs) and
`+FabiusFunction.FabiusDiscreteLimitIntegration` (3422 jobs) both exit 0 with
no warnings.  The two source leases are released; the branch may sync and
begin a new ordinary nonoverlapping claim, but receives no build token.

Synchronized registry tip `3102741f2` correctly records that acceptance.  Its
request for human-readable counterparts to the eight new declarations is a
frontier-document backlog item, not a renewed theorem-polish document lease.
The designated frontier successor may advertise that mapping as a later,
separate source phase only after the current three-hunk source/PDF disposition;
do not fold it into the narrowly granted checkpoint above.

Source commit `665b6bce` is a later one-file
`ProbabilityLaplaceMoments.lean` tranche.  It adds the generic restricted-law
reflection identity, the all-degree signed binomial transform for unit
Laplace moments, and its Fabius specialization while preserving the existing
zero-degree theorem as a compatibility wrapper.  Two independent reviews
accept the reflection orientation, signs, indices, hypotheses, API,
dependency placement, and duplicate scan.  The coordinator integrated the
exact source as `c80f61c90`.  Its first focused build exposed only recursive
`simp` use of bare `neg_pow` in the local binomial expansion and supplies no
validation evidence.  Repair `6b6757e90` names the single intended
`(-x)^j` identity explicitly, changing no theorem statement, formula, import,
or public API.  At that repaired tree,
`LAKE_JOBS=1 lake build +FabiusFunction.ProbabilityLaplaceMoments` completed
3187 jobs in 18 seconds and exited 0 without warnings.  The source lease is
released; this branch has no document or build token.

### `codex/fabius-effective-bounds-20260825`

Registry-only claim `bc14ab696` is approved for exactly
`Lean/FabiusFunction/FabiusLambertRates.lean` plus its own registry.  The six
advertised declarations are `eventually_le_dyadicLambertPhase`,
`dyadicLambertPhase_isEquivalent_id`,
`dyadicLambertPhase_inv_isEquivalent_inv`,
`smallArgumentLog_inv_isTheta`,
`isBigO_lambertScale_iff_smallArgument_log`, and
`isLittleO_lambertScale_iff_smallArgument_log`.  Independent review finds the
module/dependency blobs unchanged from the claim base, no competing path or
semantic duplicate, and the proposed equivalence chain mathematically and
topologically sound for an arbitrary normed codomain.  The first result must
be described only as an *eventual* inequality; it supplies no explicit
numerical cutoff.

Exact source commit `a8421fd7f` was integrated as `5fbdf6139`.  The first
`+FabiusFunction.FabiusLambertRates` attempt exposed only failure to eta-reduce
Mathlib's pointwise reciprocal functions and supplies no validation evidence.
Statement-preserving repair `2a5be17f3` changes the proof to an explicit
definitional `change`.  At the repaired tree, separate serialized builds of
`+FabiusFunction.FabiusLambertRates` (3252 jobs) and its narrow direct consumer
`+FabiusFunction.FabiusSharpAsymptoticTransfer` (3341 jobs) both exited 0
without warnings.  Existing headers remain unchanged; the first tranche's
source lease and codexbox token are released.

Registry-only follow-on `f3f9785fe` claims exactly
`Lean/FabiusFunction/FabiusSaddleReferenceTail.lean` plus its own registry.  It
proposes public `exp_neg_sq_centralRadius_div_four`,
`integral_norm_gaussian_add_oddCorrection_standardRadius_le_inv_pow_eight`,
and
`integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO_inv_pow_eight`,
while preserving the existing order-one Big-O theorem header as a wrapper.
Independent review verifies the standard-radius identity, constant arithmetic,
coefficient hypotheses, arbitrary-filter transport, current-main preimage,
and lack of competing active path claim.  Two corrections are binding:

- call the result the exposed **coarse eighth-order algebraic rate**, not a
  sharp rate; the Gaussian decay and the retained `1/A` factor are stronger;
- record the downstream private
  `exp_neg_sq_orderRadius_div_four` all-orders identity as known nonblocking
  semantic overlap rather than claiming no semantic match.

Exact source commit `933121538` implements the claim and was integrated as
`f85409a18`.  Three independent reviews accept the identity, constants, signs,
threshold, arbitrary-filter packaging, and weakening from `O(b⁻⁸)` to
`O(b⁻¹)`.  The source has the exact current-main preimage, changes only the
claimed module, and promotes the former private identity while adding the two
advertised estimates.  The old order-one Big-O theorem header and both direct
consumer interfaces remain byte-identical.  The prose correctly calls the rate
coarse and records the discarded `1/A` factor and downstream private overlap.
Separate serialized builds of `+FabiusFunction.FabiusSaddleReferenceTail`
(3432 jobs) and `+FabiusFunction.GaussianPolynomialTail` (3436 jobs) both exited
0 without warnings.  The source lease and codexbox token are released;
`FabiusLambertRates.lean` was not changed by this tranche.

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

The later finite-jet source checkpoint `51af7f7e1` changes exactly
`ThueMorseGenerating.lean` and `ThueMorseApproximation.lean`.  It adds the
generic finite-block/right-convolution coefficient bridge, its independent
block-depth/prefix-order specialization, and
`iteratedPrefix_eq_approximationPolynomial_coeff_all`; the old positive-order
theorem remains type- and attribute-identical as a wrapper.  Two independent
reviews found the cutoff, zero-order case, indexing, placement, API,
duplicates, imports, and scope green.  The coordinator cherry-picked only that
two-file source unit as `62ab80d03`, excluding the later speculative registry
history, and ran four serialized `LAKE_JOBS=1` targets:

- `+FabiusFunction.ThueMorseGenerating` (2085 jobs);
- `+FabiusFunction.ThueMorseApproximation` (3307 jobs);
- `+FabiusFunction.ThueMorseExponential` (2086 jobs); and
- `+FabiusFunction.PaperKFoldThueMorse` (3327 jobs).

All exited 0.  The Approximation target and facade report two nonblocking
linters: an unnecessary `simpa`, and the intentionally retained compatibility
binder `hk` is not referenced by the wrapper proof.  The two source paths are
released to this branch's already-advertised all-order same-path refinement
after it fetches/merges the new main.  Before the next source edit, correct the
worker registry's Generating evidence: the actual Git blob is `2908f1f1652e`
and content SHA-256 is
`04F8F9AB915928A98FC422C3A5048C53110FD67C29007CE55483A853561A8D9C`,
not the recorded `2412e544b` / `499A7D...`.  No build token or campaign-wide
document lease is granted for the follow-up.

Comment-only source commit `ef2430205` corrects two guide-level descriptions:
the infinite-product notation is a coefficientwise finite stabilization, and
the order-zero cutoff admits only index zero rather than making the series
one-term.  Mechanical comparison proves that every byte outside the two
leading module comments is unchanged; the coordinator integrated this exact
commit as `5d779327a`, so no Lean build is required for that prose-only unit.

The branch's ordinary claim covered exactly three source paths:
`FabiusQBinomialTaylor.lean`, `ThueMorseGenerating.lean`, and
`ThueMorseApproximation.lean`.  The seven declarations are
the four translated-power-sum Appell APIs
`thueMorseTranslatedPowerSumPolynomial_comp_X_add_C`,
`thueMorseTranslatedPowerSumPolynomial_hasseDeriv`,
`thueMorseTranslatedPowerSumPolynomial_derivative`, and
`thueMorseTranslatedPowerSumPolynomial_derivative_succ`, plus
`one_sub_X_pow_mul_approximationPolynomialInt_all`,
`thueMorseBlockPolynomial_mul_invOneSubPow_eq_approximationPolynomialInt`, and
`correctedPrefixCoefficient_eq_stepApproximant_all`.  No competing path or
plausible-name claim was found.  The earlier convolution bridges and
`iteratedPrefix_eq_approximationPolynomial_coeff_all` are already integrated
and compiled context; do not reimplement them.  The corrected Generating blob
evidence is `2908f1f1652e` / SHA-256 `04F8F9AB...A8D9C`.

Source commit `8021c555f` implements the four Appell declarations in
`FabiusQBinomialTaylor.lean`; its parent matches main blob `4032b5184` and its
result blob is `52492287b`.  Two independent reviews accept the finite
translation law, total Hasse law, derivative specializations, every boundary
case, imports, API, placement, and duplicate scan.

Source commit `f7152d5fc` independently implements the three total
approximation declarations in `ThueMorseApproximation.lean`; its parent matches
main blob `87023172f` and its result blob is `d2e85228f`.  Two independent
reviews accept the polynomial and formal-series identities at `k = 0`, the
case-free coefficient and normalized-step bridges, the strict cutoff, private
helper deletion, and exact preservation of all old public wrapper headers and
attributes.  Registry tip `b52fa523e` freezes both source units on a branch
already synchronized through main `99b67cf5b`.

**EVO validation grant.**  This branch now holds the sole EVO token.  From a
clean pushed tree, merge this coordinator checkpoint, verify that the two
source blobs remain exactly `52492287b` and `d2e85228f`, and run these as three
separate sequential invocations with `LAKE_JOBS=1`:

```text
lake build +FabiusFunction.FabiusQBinomialTaylor
lake build +FabiusFunction.ThueMorseApproximation
lake build +FabiusFunction.PaperKFoldThueMorse
```

Do not run them in parallel and run no additional Lean/Lake/TeX/PDF target.  If
one fails, do not run the later targets or edit source under the same token;
record the complete first failure in the own registry, push, and stop.  If all
three pass, record exact SHA/tree, commands, job counts, warnings, and exits in
the own registry, push, and stop for coordinator integration.  Never push
`main`.

**Validation and integration result.**  Registry checkpoint `b28da9013`
records the completed EVO run at exact merge `4367a7f86`, tree `db635e6a073b`.
The three required separate `LAKE_JOBS=1` targets completed in order:

- `+FabiusFunction.FabiusQBinomialTaylor`: 3320 jobs, exit 0, no warnings;
- `+FabiusFunction.ThueMorseApproximation`: 3307 jobs, exit 0, only the two
  known unused-`hk` compatibility linters;
- `+FabiusFunction.PaperKFoldThueMorse`: 3327 jobs, exit 0, replaying only
  those two linters.

No later source edit occurred.  The coordinator integrated only exact source
commit `8021c555f` as `30cc17175`, then exact source commit `f7152d5fc` as
`ca3a0dca5`; the divergent feature history and registry were not merged.
Every claimed source path and the EVO token are released.  The branch may sync
and begin a new ordinary nonoverlapping claim, but has no current source or
build ownership.

### `codex/fabius-exposition-integration`

Checkpoint `5e0505bf2` was merged to `main` by `ccf81cf83` while the
documentation freeze was active.  Its later merge at `1570b29b9` contributes
only `docs/registry/codex-fabius-exposition-integration.md` relative to the
coordinator checkpoint; it does not change an exposition or frontier artifact.
That registry's useful audit body is retained, while its `cffe24808` snapshot
and expired current-tree/page-count statements are now labeled explicitly.

**Former single-owner frontier lease.**  The staged frontier work had spanned
only:

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

**Stage-two result.**  The branch merged this board cleanly at `1ca2a09be`
without changing the accepted TeX, then ran exactly the three authorized
sequential `pdflatex` passes with a fresh `_stage2` job name.  All exited 0;
page counts were 178, 186, and 186.  The third pass settled every reference and
citation and reported no duplicate label, horizontal overfull box, rerun,
changed-label, fatal, or LaTeX-error diagnostic.  It did report exactly one
`Overfull \\vbox (59.28255pt too high)` immediately before output page 184.
The worker correctly stopped without a fourth pass, TeX/README edit, canonical
PDF replacement, or primary cleanup.  Checkpoint `e6ac85e2f` records the exact
evidence; the rejected PDF and log remain sidecar-preserved under `_stage2`.
No validation claim or PDF acceptance is made from that run, and its EVO tool
token is released.

**Narrow source-repair result.**  After merging the repair directive cleanly,
source commit `5fee1bb90` changes exactly one locally scoped token in the
single indivisible formal-background `tabularx`: `\\small` becomes
`\\footnotesize` inside its existing group.  The preserved log/PDF show that
this table was deferred from page 183 and exceeded a fresh page 184 by
59.28255pt; shrinking roughly sixty local baselines directly addresses that
measured excess.  No row, prose, mathematics, status, label, reference,
citation, environment, README, PDF, or global typography changes.  The new
TeX SHA-256 is
`D6791ED6AA0246EE9986D67BDF0BCC9823D431E46CAEA1FEE34409FEB25D16DA`.
Checkpoint `87bf890d3` is clean, records unchanged static predicates, and is
independently accepted for a fresh build.

**Stage-three grant.**  This branch again holds the sole EVO tool token for the
canonical frontier only.  From clean tip `87bf890d3`, use a fresh
`non-formalized-research-frontiers_stage3` job name and run exactly three
sequential invocations of the same recorded `pdflatex` command.  Run no Lean,
Lake, `latexmk`, other TeX compiler, or fourth pass.  The third pass must have
settled references/citations, zero rerun or changed-label diagnostics, zero
duplicate labels, zero overfull horizontal **and vertical** boxes, and no
fatal/LaTeX error.  After the third pass only, read-only `pdfinfo`, `pdffonts`,
text extraction, and page rasterization are permitted for validation.  Require
all fonts embedded; inspect page 184 for table legibility, clipping, footer
collision, and surrounding page breaks, and recheck page 10 plus every changed
semantic cluster.

If every gate passes, replace the canonical frontier PDF with the exact settled
stage-three bytes, record the three commands/exits/page counts, log/PDF hashes
and sizes, all diagnostic counts, font/text/raster evidence, visual inspection,
Git blob, and clean status in the branch registry, then commit only that PDF
and registry and push the feature branch.  If any gate fails, do not perform a
fourth pass or edit source: preserve the artifacts, report the exact failure in
the registry, and stop.  Never push `main` or begin primary cleanup.

The frontier README/TeX and the 57-page primary exposition remain fully frozen
during stage three.

**User scope override.**  The stage-three invocations finished before a later
explicit narrowing, but their generated frontier PDF was never copied,
staged, committed, or pushed.  It must remain sidecar-only and receives no
coordinator review, validation, or integration claim.  All further frontier
work and all primary claim/layout auditing stop in this task; another worker
owns any frontier continuation.  The frontier lease and stage-three token are
released.

**Primary compile-only result.**  The branch merged main `682222de1`
conflict-free at clean pushed tip `6397a0d6a`.  The unchanged primary source
has Git blob `e3a0df24e` and SHA-256
`F4EE348F21524C2EDB8880E16E50802CCC6A3A831D38C8426F23AF7607EA64F1`.
Exactly three fresh `pdflatex` passes used the authorized sidecar job name and
all exited 0.  The final output has 57 pages, with zero undefined
references/citations, rerun requests, changed-label warnings, fatal errors, or
LaTeX errors.  Its extracted text is byte-identical to the tracked canonical
PDF, so the worker correctly avoided timestamp-only canonical-PDF churn.  No
primary source/PDF or generated frontier PDF was staged.  This is compile
confirmation only, not a claim/layout audit.

After that scope close, merge tip `6397a0d6a` independently advanced `main`
and made the branch's frontier README, TeX, and registry source checkpoint
reachable.  It changed neither the frontier PDF nor any primary path.  Preserve
the forward history, but do not treat the resulting mismatched frontier
TeX/PDF pair as a validated final artifact: the user-designated successor owns
its disposition and any matching rebuild.

The exposition task is complete under the user's narrowed scope.  Its EVO
token and all document ownership are released.  Do not resume its frontier or
primary work; any successor frontier owner must be identified separately on
this board.

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

No reviewed Lean workstream is waiting on an assigned validation token.  The
four disjoint both-papers units, periodic bridges, all-index oddness, private
spline cleanup, reflected Laplace moments, and the shifted-prefix seven-name
tranche are integrated and validated as recorded above.  Continue to avoid
merging either moving feature history wholesale.  The generic Rvachev bridge
and Lambert-rate equivalence tranches are also integrated, repaired, compiled,
and released.  The all-degree complex branch theorem, its downstream all-real
continuation, and the disjoint coarse eighth-order reference-tail tranche are
integrated, compiled, and released.

Theorem-polish source commit `665b6bce` is integrated as `c80f61c90`, repaired
without statement changes at `6b6757e90`, and accepted after its focused
3187-job build exited 0.  Its `ProbabilityLaplaceMoments.lean` lease is
released.

Frontier source checkpoint `6397a0d6a` is already on `main` without a matching
rebuilt PDF historically; accepted merge `192c423bb` now closes that mismatch
with the reviewed 188-page artifact.  No documentation worker or codexbox
TeX/PDF lane is currently assigned, so every canonical document path is
frozen pending a new exact-path claim and board assignment.  EVO is idle after
the green shifted-prefix run.  Ordinary
nonoverlapping feature claims may continue under the shared protocol, but no
Lean/Lake process may start on either physical host until this board assigns
that host's currently idle token.

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

At exact both-papers integration merge `04d619814`, the coordinator ran ten
separate serialized targets: `+FabiusFunction.DyadicAnalytic` (2772 jobs),
`+FabiusFunction.GlobalExtension` (2765), `+FabiusFunction.GlobalDyadic`
(2785), `+FabiusFunction.OriginalPaperSupplement` (3210),
`+FabiusFunction.BoseFinitePartIntegral` (3268),
`+FabiusFunction.PeriodicMean` (3269),
`+FabiusFunction.PeriodicRegularity` (3295),
`+FabiusFunction.PeriodicSmooth` (3297), `+FabiusFunction.Paper05442` (3417),
and `+FabiusFunction.PaperFabiusAsymptotic` (3957).  All used `LAKE_JOBS=1`
and exited 0.

At finite-jet source checkpoint `62ab80d03`, the coordinator ran
`+FabiusFunction.ThueMorseGenerating` (2085 jobs),
`+FabiusFunction.ThueMorseApproximation` (3307),
`+FabiusFunction.ThueMorseExponential` (2086), and
`+FabiusFunction.PaperKFoldThueMorse` (3327) serially; all exited 0.  The
Approximation module reports only the two documented nonblocking compatibility
linters.

For the discrete-shift tranche, the first Toeplitz attempt at `de8707b44`
failed on proof elaboration and supplies no validation evidence.  After repair
`8e09c4d98`, `+FabiusFunction.FabiusDiscreteLimitToeplitz` (3320 jobs) and
`+FabiusFunction.FabiusDiscreteLimitIntegration` (3422 jobs) both exited 0
without warnings.

For the four later both-papers units, the coordinator retained the sole
codexbox token and ran each required target in a separate `LAKE_JOBS=1`
invocation on the exact cumulative coordinator tree:

- at `f975de00f`, `+FabiusFunction.AnalyticMoments` completed 2828 jobs,
  exit 0;
- at `f62058b96`, `+FabiusFunction.FourierProduct` completed 3190 jobs,
  exit 0;
- at `29729991e`, `+FabiusFunction.HalfQBinomial` completed 2020 jobs and
  `+FabiusFunction.FabiusQBinomialFormula` completed 3317 jobs, both exit 0;
- at `6f98e4804`, `+FabiusFunction.FabiusSharpAsymptotic` completed 3891 jobs
  and `+FabiusFunction.PaperFabiusAsymptotic` completed 3957 jobs, both exit 0.

Before the green AnalyticMoments invocation, the same command was issued once
from `Analysis/FabiusFunction/Lean`, which has no Lake configuration.  It
exited 1 immediately without launching Lean and supplies no evidence.  All
subsequent commands used the repository root.

For the periodic derivative bridges, the first
`+FabiusFunction.PeriodicSmooth` attempt at `af3132a31` exited 1 on the two
documented proof-elaboration defects and supplies no validation evidence.
After statement-preserving repair `8d269396a`, the same serialized target
completed 3297 jobs and exited 0 without warnings.

For all-index oddness, `+FabiusFunction.Paper06487Supplement` at
`6d15d9116` completed 3243 jobs and
`+FabiusFunction.Paper06487` completed 3244 jobs, both exit 0.  For the dead
private spline-helper cleanup, `+FabiusFunction.FabiusUniformSpline` at
`b16fc9a6d` completed 3415 jobs, exit 0.

For all-order reflected Laplace moments, the first
`+FabiusFunction.ProbabilityLaplaceMoments` attempt at `c80f61c90` exited 1
because bare `simp [neg_pow]` recursively reconsidered its generated
`(-1)^j` factor; it supplies no validation evidence.  After the
statement-preserving explicit-identity repair `6b6757e90`, the same serialized
target completed 3187 jobs in 18 seconds and exited 0 without warnings.

For the generic Rvachev bridge, the first
`+FabiusFunction.Differential` attempt at `12fda28c7` exited 1 because
unrestricted simplification unfolded `fabiusReal` before applying the generic
left-tail hypothesis at `rvachevUp F 1`; it supplies no validation evidence.
Repair `15563b7dd` states the two fold-endpoint zeros explicitly without
changing a theorem statement.  At that tree, separate serialized builds of
`+FabiusFunction.Differential` (2653 jobs) and `+FabiusFunction.Existence`
(2783 jobs) both exited 0 without warnings.

For reciprocal Lambert rates, the first
`+FabiusFunction.FabiusLambertRates` attempt at `5fbdf6139` exited 1 because
`simpa` did not eta-reduce Mathlib's pointwise inverse functions; it supplies
no validation evidence.  Repair `2a5be17f3` makes the definitional function
shape explicit, changing no public statement.  At that tree, separate
serialized builds of `+FabiusFunction.FabiusLambertRates` (3252 jobs) and
`+FabiusFunction.FabiusSharpAsymptoticTransfer` (3341 jobs) both exited 0
without warnings.

For the all-degree complex branch estimate, separate serialized builds at
`f6cb1efd8` of `+FabiusFunction.FabiusDiscreteLimitComplexShift` (1873 jobs)
and `+FabiusFunction.FabiusComplexShiftSpline` (3417 jobs) both exited 0
without warnings.

For the downstream all-real complex-spline continuation, a serialized build at
`19ee18206` of `+FabiusFunction.FabiusComplexShiftSpline` completed 3417 jobs
and exited 0 without warnings.

For the coarse eighth-order reference-tail tranche, separate serialized builds
at `f85409a18` of `+FabiusFunction.FabiusSaddleReferenceTail` (3432 jobs) and
`+FabiusFunction.GaussianPolynomialTail` (3436 jobs) both exited 0 without
warnings.  An earlier command issued from a directory without a Lake project
configuration exited before invoking Lean and supplies no validation evidence.

On EVO, exact shifted-prefix merge `4367a7f86` and tree `db635e6a073b`
preserved source commits `8021c555f` and `f7152d5fc`.  Separate sequential
`LAKE_JOBS=1` builds of `+FabiusFunction.FabiusQBinomialTaylor` (3320 jobs),
`+FabiusFunction.ThueMorseApproximation` (3307 jobs), and
`+FabiusFunction.PaperKFoldThueMorse` (3327 jobs) all exited 0.  The latter two
reported only the two intentionally retained unused-`hk` compatibility
linters.  No fourth target or overlapping process ran; the EVO token is
released.

On EVO, stage two at source tip `1ca2a09be` ran exactly three sequential
frontier `pdflatex` passes under the authorized fresh `_stage2` job name.  All
three exited 0 and produced 178, 186, and 186 pages.  The third pass was
reference/citation-stable and free of duplicate labels, horizontal overfull
boxes, rerun requests, changed labels, and fatal/LaTeX errors, but it contained
one 59.28255pt overfull `\\vbox` immediately before page 184.  The worker
stopped and preserved the rejected PDF/log without touching the canonical PDF.
This run fails the zero-overfull-box gate and grants no PDF validation; its
token is released pending a source-only repair checkpoint.

The exposition branch later completed the authorized three stage-three
frontier passes, but before any canonical copy, staging, evidence commit, or
push the user explicitly ended frontier work in that task.  The generated PDF
and log remain sidecars.  They are not reviewed or accepted here, and no
frontier validation or integration claim follows from them.

The subsequent compile-only primary check at source blob `e3a0df24e` ran three
fresh `pdflatex` passes, all exit 0.  Final output was 57 pages with no undefined
reference/citation, rerun, changed-label, fatal, or LaTeX-error diagnostic.
Extracted text matched the tracked canonical PDF byte-for-byte, so no PDF was
replaced or staged.  This closes only the requested compilation confirmation.

Before those green runs, one command launched from the wrong directory was a
no-op, and the first correctly rooted attempt exhausted the filesystem while
creating a fresh `.lake`; it exited 1 and supplied no validation evidence.
The coordinator removed only that generated failed cache, then copied an idle
worktree's dependency cache and reran at the immutable source tree.  During the
worker checkpoint, `/home/codex/src/Proofs` also launched an unassigned
`lake env lean` prototype check; it exited and is not treated as integration
evidence.

No validation process was running on codexbox when the original PDF grant was
published.  A lightweight sequential TeX/PDF lane is independent of the
one-process codexbox Lean/Lake token when the board assigns a document owner;
both codexbox lanes are currently idle, and the Lean/Lake token remains
coordinator-owned.  EVO's Lean/Lake token is also idle and unassigned after
the completed shifted-prefix run.  Other branches may edit, checkpoint, and
push ordinary claimed work under the open protocol, but may not run Lean/Lake
or a document tool stream until this board assigns the applicable lane.

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
