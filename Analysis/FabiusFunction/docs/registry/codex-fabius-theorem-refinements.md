# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at
  published checkpoint 996ef24218fd11d2f76984292bde534cd13eefc9,
  with pinned origin/main a24af8347aba5d38b8febf2cf9a19eeef6aba18a
  resolved for the current merge checkpoint
git owner: root in this worktree
build owner: not held; incoming commit d29ca2fe7 reports an aggregate build of
  the exact incoming Lean subtree, but no build has been run on the resolved
  996ef2421 + a24af8347 union.  Recheck and claim the host-wide lane before any
  focused or aggregate replay
source lease: refreshed 2026-08-25 13:02 -07:00 through 14:02 -07:00
next synchronization checkpoint: publish this pinned merge, re-fetch
  origin/main, and record whether the remote pin remained current; then pursue
  the exact combined-tree Lean replay under the single build owner
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
- Fourth integration lease for pinned main `a24af8347` over published
  checkpoint `996ef2421`: retain the incoming exact differentiability and
  finite/`C∞` smoothness locus in `FabiusInverse.lean`, the all-orders-flat
  remainder equivalence, the vector-valued small-argument transport API, and
  the proof-normalization changes.  Preserve the branch-only translated-
  polynomial coefficient/zero/degree API.
- Semantic artifact repair lease for this nontrivial merge:
  `docs/Non_Elementarity_of_the_Fabius_Function/Non_Elementarity_of_the_Fabius_Function.{tex,pdf}`,
  `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.{tex,pdf}`,
  `docs/non-formalized-research-frontiers/Repeated_Integration_and_Rvachev_Up/Repeated_Integration_and_Rvachev_Up.{tex,pdf}`,
  `docs/registry/claude-fabius-non-elementary-proof-861d70.md`, and this active
  registry.  This covers semantic conflict resolution, stale-reference repair,
  explicit formalization boundaries, reproducible PDF rebuilds, and immutable
  validation attribution.

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

Each substantive non-merge checkpoint message records its exact textual
validation and any deferred Lean targets.  Incoming commits `b164f3d2f` and
`c62a56d95` report focused and aggregate validation of the core inverse
calculus and smoothness, while the other incoming mathematical lanes likewise
carry focused immutable evidence.  Those reports predate the current-only
translated-polynomial batch and do not validate the exact combined
`4b8c0094e + 783cecf720` tree.

## Current merge-checkpoint evidence

For the exact source-resolved `996ef2421 + a24af8347` tree, all 12 incoming
Lean files retain `set_option autoImplicit false`.  The tree-wide forbidden
declaration/placeholder and conflict-marker scans, `git diff --check`, and the
local-Markdown-link scan are clean.  Relocated small-argument references use
the research-frontier path.  The documentation ratchet passes with 188
modules, 3,158 public declarations, 159 existing missing comments in 17 files,
and no missing module headers.

Three changed articles were rebuilt with three successful PDFLaTeX passes and
inspected at representative rendered pages:

- the primary synthesis is 166 A4 pages, has 810 unique labels and 1,428
  resolved references, and has PDF SHA-256
  `0D6E83E7268810FEB72E2136905B4632C179FB5B4D5F3DC1C681550CA5348573`;
- the non-elementarity paper is 14 A4 pages, has 23 unique labels and 86
  resolved references, and has PDF SHA-256
  `D29CDCCDB4EE26CD0DAADC312534E3613A0BFF5C31051F96101E4C6AFC7D86FB`;
- the repeated-integration research frontier is 20 A4 pages, has 122 unique
  labels and 75 resolved references, and has PDF SHA-256
  `718D848AB32D8ED174A27DBB582558E33A307531F81995D73379680408C7966A`.

The primary log has only pre-existing harmless `hyperref` bookmark-token
warnings; the non-elementarity log has three underfull-box diagnostics; the
frontier log is clean.  There are no undefined references, duplicate labels,
fatal errors, or overfull boxes in these rebuilt documents.

Incoming commit `d29ca2fe7` reports a clean-tree, single-job, 4,007-job
aggregate `+FabiusFunction` build.  The Lean subtree at that commit is exactly
the subtree at incoming tip `a24af8347`.  This is strong immutable evidence for
the incoming side only: it does not compile the branch-only translated-
polynomial batch or the exact resolved union, whose Lean replay remains
pending.

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
gate passed.  The fourth pinned integration at `a24af8347` is source-resolved
over published checkpoint `996ef2421`; active ownership is unchanged, and
focused Lean validation of the exact combined tree remains pending until this
merge is published and the host-wide build lane is rechecked and claimed.
