# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at
  unpublished merge checkpoint 4c54e8d9beee1622003891222b76e2cfc59b685f,
  merging pinned origin/main 6fcbbb5da45330bdc78c6090706cf1479f3d3afb
git owner: root in this worktree
build owner: external 10ef worktree; this worktree will not run Lean, Lake, or
  cache-mutating commands until that owner records a terminal event
source lease: refreshed 2026-08-25 15:37 -07:00 through 16:37 -07:00 for the
  exact 6fcbbb5d documentation merge and registry repair paths below
next synchronization checkpoint: resolve, rebuild, inspect, commit, and
  publish this pinned merge; then re-fetch origin/main and merge any newer
  exact tip before a no-force fast-forward push to main
```

## Current integration and validation lease

- `Lean/FabiusFunction/FabiusQBinomialTaylor.lean`: the reviewed all-index
  coefficient, zero, natural-degree, degree, leading-coefficient, and boundary
  APIs, together with the redundant-`CharZero` cleanup, are published at
  `a95bd1913`; this lease is retained only for merge repair and the pending
  focused combined-tree build.
- `README.md`: the translated-polynomial documentation is published at
  `a95bd1913`; this merge also leases the inverse-branch prose corrections
  listed below.
- `docs/AUDIT_FINDINGS.md`: close the verified redundant-`CharZero` API
  finding.
- `docs/COLLABORATION.md`: retire the translated-polynomial candidate once the
  theorem batch is compiled and published.
- `docs/registry/codex-fabius-theorem-refinements.md`: this status record.
- Sixth integration lease for pinned main `f51777a1` over published checkpoint
  `1b2cd37d`: retain the incoming effective cumulant bounds, generalized
  Laplace/reflection identities, representation-independent inverse dyadics,
  all-node q-Pochhammer evaluations, parameter-dependent scalar transport,
  full left-tail Thue--Morse convergence, and Fourier/Poisson symmetries.
  Preserve the branch-only translated-polynomial coefficient/zero/degree API.
- Semantic artifact repair lease for this nontrivial merge:
  `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.{tex,pdf}`,
  `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.{tex,pdf}`,
  their provenance README, the retired frontier paths, both Codex registries,
  and this active registry.  This covers semantic conflict resolution,
  consolidation without data loss, stale-reference repair, explicit
  formalization boundaries, reproducible PDF rebuilds, and immutable
  validation attribution.
- Seventh integration lease for pinned main `6fcbbb5d` over unpublished
  checkpoint `4c54e8d9`: retain the incoming theorem/API union and synthesized
  dossier structure; semantically reconcile the primary module guide,
  formalization boundaries, provenance registry, and both generated PDFs.

## Read-only survey

- `ThueMorsePrefix.lean`, `ThueMorseExponential.lean`,
  `ThueMorseGenerating.lean`, and `FabiusUniformSpline.lean` for existing
  sharp-moment and real-scalar APIs;
- `ProbabilityLaplaceMoments.lean`, `FabiusComplexMGF.lean`, and their callers
  to avoid reintroducing transform bridges already integrated upstream; and
- `AlgebraicBranch.lean` and `NotElementary.lean`, whose completed localized
  algebraic-branch implementation is integrated at `0f1a20a7c` and whose
  historical registry was closed at `3de52ca1c`, to avoid duplicating that
  theorem family; and
- current branch registry files and advertised remote tips before expanding
  either write set.

## Completed and published checkpoints

- `b49741f22`: exact affine sharp-degree Thue--Morse moment and consumer
  refactors; its equivalent mainline form is now integrated upstream.
- `44bdcbd8e`: canonical real-input complex generating bridge with a deprecated
  compatibility alias and migrated callers; the resulting API is now also on
  mainline.
- `1567c96b4`: all-real probability/support documentation and repaired paper
  entry points.
- `09885a710`: one operational coordination authority, immutable synchronization
  pins, direct-main authorization boundaries, and explicit feedback routes.
- `fdae28cab` on mainline now supplies the arbitrary-complex MGF derivative
  bound and keeps the vertical-line theorem as a compatibility wrapper, so the
  provisional transform candidate on this branch is retired.
- `a049141fb` on mainline supplies the unified rational affine and translated
  power-sum API; the distinct formal-polynomial coefficient/zero/degree batch
  remains open and should build on those names.
- `0f1a20a7c` on mainline integrates the localized algebraic-branch
  implementation, including the direct nowhere-analytic corollaries;
  `3de52ca1c` closes its historical registry, so the formerly advertised work
  is no longer an open lane.
- `5e80805b1` on mainline integrates the foundational/Fourier/probability and
  finite-remainder generalizations.  In particular `cfc70e3bc` factors the
  q-binomial refinement coefficient argument by degree without consuming the
  separate translated-polynomial coefficient/zero/degree lane leased here.
- `a95bd1913` on this branch publishes the exact translated-polynomial
  coefficient, zero, degree, leading-coefficient, and boundary-normal-form API,
  plus the redundant-`CharZero` cleanup and matching README documentation.
- `ad6cf6a07` publishes the first pinned-main integration at `1e371c773`, with
  the translated-polynomial batch retained and its exact combined-tree Lean
  validation explicitly deferred.
- `4b8c0094e` publishes the second pinned-main integration at `639bfc53e`, with
  the right-inverse/interior-complement API resolved coherently, the
  non-elementarity paper rebuilt and inspected, and exact combined-tree Lean
  validation explicitly deferred behind the then-active external build owner.
- `996ef2421` publishes the third pinned-main integration at `783cecf720`, with
  the core inverse calculus and conditional inverse-branch documentation
  reconciled, the non-elementarity paper rebuilt, and the new dyadic/q
  research-frontier article supplied with a rendered PDF.  Its exact combined
  Lean replay was explicitly deferred.
- `23bfd95d0` publishes the fourth pinned-main integration at `a24af8347`, with
  exact inverse smoothness, all-order flat-remainder and vector-valued
  small-argument APIs retained, three documentation artifacts rebuilt and
  inspected, and exact combined-tree Lean validation explicitly deferred.
- `1b2cd37dd` publishes the fifth pinned-main integration at `35852aa65`, with
  the incoming theorem families retained, both conflicted papers rebuilt and
  inspected, and the primary exposition restored to its proof-backed boundary;
  exact combined-tree Lean validation remained explicitly deferred.

Each substantive non-merge checkpoint message records its exact textual
validation and any deferred Lean targets.  Incoming commits `b164f3d2f` and
`c62a56d95` report focused and aggregate validation of the core inverse
calculus and smoothness, while the other incoming mathematical lanes likewise
carry focused immutable evidence.  Those reports predate the current-only
translated-polynomial batch and do not validate the exact combined
`23bfd95d0 + 35852aa65` tree.

## Sixth pinned integration evidence (historical)

This checkpoint merges exact incoming tip
`f51777a184240e20d5991676ebb3465b0824b942` into exact published branch
checkpoint `1b2cd37ddad9253cb498510f99368f68eeac5b99`.  The merge base is
`35852aa65ba66cf700419c296a78460b02bb65b3`; the sides were 13 and 33 commits
ahead of that base.  Git reported six true conflict paths: the primary source
and binary, plus four modify/delete paths from the incoming frontier
consolidation.  No Lean source has a conflict; the independently edited
`InverseNotElementary.lean` hunks merge disjointly.

The incoming range changes 22 Lean modules and exposes 70 additional public
declarations after accounting for two formerly private generalized lemmas.
No public declaration is removed or weakened.  The new APIs cover effective
Laplace and dyadic-cumulant bounds, reflection moments, inverse curvature and
representation-independent dyadics, complete half-base q-evaluations,
parameter-dependent asymptotic transport, full left-tail Thue--Morse
convergence, and Fourier/Poisson symmetries.  All 188 modules retain
`set_option autoImplicit false`.  The merge also repairs the incoming
documentation-ratchet regression by documenting `partialSum_smul`.

The primary synthesis keeps the strict proof-backed boundary and proved
top-mass-jet theorem while adding the incoming inverse second derivative,
closed-half curvature, all-order endpoint steepness, primitive Thue--Morse
recursion, and expanded real module guide.  Both stale small-argument paths now
name Part “Small-Argument Asymptotics Research Frontiers” in the canonical
consolidated source.  The regenerated primary PDF is 76 A4 pages with SHA-256
`1A8DD39F85412C723A9C8E86A4A89B41E0C0A3D01B3462A069B4E6E8D57B3822`.

The incoming consolidation retires eleven standalone source notebooks without
losing the two branch-later refinements: the detailed dyadic-q formalization
boundary and source map, and the repeated-integration formalization boundary
and corrected finite-atomic/spline wording, are transplanted into their
namespaced canonical parts.  Their provenance hashes are updated to
`8776344b...` and `e3a7fcad...`; the duplicate Rvachev source already matched
the consolidated `fad16072...` hash.  The regenerated canonical frontier PDF
is 273 A4 pages with SHA-256
`F4BBB2B69150A3261E70F2BC7CFCE6B45EF451555746829B51D864FBD4D293AB`.

Both changed documents received exactly three successful PDFLaTeX passes and
representative rendered-page inspection.  Their final logs contain no
undefined references or citations, multiply defined labels, rerun notices,
fatal errors, or overfull boxes.  The primary retains twelve benign hyperref
bookmark-token warnings and one underfull box; the consolidated volume has
only underfull diagnostics.

Post-resolution static gates are clean: working/index `diff --check`, the
tree-wide conflict-marker and forbidden declaration/placeholder scans, 47
local Markdown links, and all five project-authored TeX/PDF pairs.  The
documentation ratchet passes at 188 modules, 3,251 public declarations, 156
pre-existing undocumented declarations in 17 files, and zero missing module
headers.

Incoming components carry focused immutable build evidence, but the final
incoming tip only reports focused `LaplaceMomentBounds` and `FabiusInverse`
builds.  Its older aggregate claim predates 13 later Lean-file changes.  On the
exact manually resolved union, serialized builds of
`+FabiusFunction.FabiusQBinomialTaylor` (3,320 jobs) and
`+FabiusFunction.FabiusQBinomialFormula` (3,317 jobs) both completed at exit
zero.  A subsequent `FabiusInverseDyadicClosedForm` Lake graph scan ceased
making measurable CPU progress with about 800 MB host memory free; the current
worktree's wrapper was interrupted before any Lean child started, its mutex was
released, and zero residual Lean/Lake processes remained.  The remaining
changed-leaf replay, umbrella target, and axiom audit are therefore explicitly
resource-deferred, not inferred from historical artifacts.

## Seventh pinned integration evidence

This checkpoint merges exact incoming tip
`6fcbbb5da45330bdc78c6090706cf1479f3d3afb` into exact local checkpoint
`4c54e8d9beee1622003891222b76e2cfc59b685f`, with merge base
`f51777a184240e20d5991676ebb3465b0824b942` and divergence of 14 branch-only
and 29 incoming-only commits. An immutable preview and the actual merge agree
on five conflict paths, all documentation: the primary and consolidated
frontier TeX/PDF pairs and the historical both-papers registry. No Lean source
conflicts.

The incoming Lean union adds a generic unit-Laplace-moment abstraction,
computable signed-global splines, boundary-complete binary/Bernoulli APIs,
quantitative saddle transfers, lower-Lambert calculus, Bose finite-part
integrals, and logarithmic small-argument refinements. A lexical public-name
comparison finds 97 additions and no removal from this branch's prior public
surface. The facade auto-merge retains the corrected frontier link and adds
the new focused import.

The primary resolution keeps the complete sharp-asymptotic module family,
adds the Mellin/Bose modules, retains the incoming Bose and signed-global
accounts, and pins its bibliography to theorem-bearing commit `169de0901`.
Its three-pass rebuilt PDF is 78 A4 pages with SHA-256
`AE8742EA8D254F4318347F9C0C18FA327D159493FDABB211DBF8F6386B45CDB1`.
The frontier uses the incoming deduplicated repeated-integration, Thue--Morse,
and dyadic synthesis, with explicit local warnings for paper-level results
that still lack exact declarations. Its synthesized provenance records the
repaired repeated-integration and dyadic-q source hashes `e3a7fcad...` and
`8776344b...`. Its final three-pass rebuilt PDF is 192 A4 pages with SHA-256
`411309202A8789D58B6D4690D8AB054DD8184CAC75AD86D51F8686B4956614EE`.
Both final logs have no undefined references or citations, duplicate-label
rerun requests, fatal errors, or overfull boxes; representative changed pages
were rendered and inspected. The incoming 88-page walkthrough source/PDF pair
is preserved byte-for-byte.

Post-resolution static gates pass: staged and unstaged `diff --check`, a
tree-wide conflict-marker scan, the forbidden Lean declaration scan, all 189
leaf modules with `autoImplicit false`, 48 local Markdown links, and all five
project-authored TeX/PDF pairs. The documentation ratchet reports 189 files,
3,348 public declarations, 154 pre-existing undocumented declarations in 16
files, zero missing module headers, and no regression. Exact-tree Lean
compilation remains explicitly deferred while the 10ef worktree owns the
single host-wide build lane; historical incoming and pre-merge component
builds are not represented as validation of this merged union.

## Reviewed translated-polynomial API

Independent mathematical/API review and a separate hostile source preflight
confirmed the following coherent declaration family:

- an exact coefficient formula in terms of
  `thueMorseCenteredPowerSum k (d - j)`;
- vanishing exactly when `d < k`; and
- the all-index degree drop `natDegree = d - k`, the exact `WithBot`-valued
  degree and leading coefficient, and the `k = 0` and `d = k` normal forms.

The reviews checked `k = d = 0`, `k = 0`, `d < k`, `d = k`, `j > d`, the
nonzero leading coefficient, simp critical pairs, and the four redundant
`CharZero` binders.  The hostile preflight found and repaired one associativity
mismatch in the sharp-coefficient nonzero proof, then found no remaining
source-level blocker against the exact Mathlib signatures and import closure.
On the pre-merge `a95bd1913` tree, `git diff --check`, the
forbidden-placeholder/conflict-marker scans, and the documentation baseline
gate passed.  The sixth pinned integration at `f51777a1` is source-resolved
over published checkpoint `1b2cd37d`; active ownership is unchanged, and
focused Lean validation of the exact combined tree remains pending until this
merge is published and the host-wide build lane is rechecked and claimed.
