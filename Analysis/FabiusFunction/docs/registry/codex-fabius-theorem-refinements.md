# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at
  published checkpoint 4b8c0094ed382d896390907d3703cadf8138cc19,
  with pinned origin/main 783cecf7208edd4de86fd0cee7d4b9f13299ee60
  integrated for the current merge checkpoint
git owner: root in this worktree
build owner: not held; the external guarded non-elementarity closure reported
  its terminal 35-module rebuild and axiom audit, and a read-only host process
  check at 2026-08-25 11:55 -07:00 found no live lean, lake, or closure-driver
  process.  Recheck immediately before claiming the lane
source lease: refreshed 2026-08-25 12:04 -07:00 through 12:34 -07:00
next synchronization checkpoint: publish this pinned merge and re-fetch
  origin/main; once the pin remains current, claim the host-wide lane for the
  exact combined-tree focused Lean build
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
- Third integration lease for pinned main `783cecf720` over published
  checkpoint `4b8c0094e`: retain the incoming core inverse calculus in
  `FabiusInverse.lean`, including `fabiusInv_hasDerivAt`, its compatibility
  spelling, the exact positive derivative, and `fabiusInv_contDiffOn_Ioo`;
  keep only the noncritical and non-representability layer in
  `InverseNotElementary.lean`.
- Semantic artifact repair lease for this clean textual merge:
  `docs/Non_Elementarity_of_the_Fabius_Function/Non_Elementarity_of_the_Fabius_Function.{tex,pdf}`,
  `docs/non-formalized-research-frontiers/Fabius_Dyadic_q_Connections/Fabius_Dyadic_q_Connections.{tex,pdf}`,
  `docs/registry/claude-fabius-non-elementary-proof-861d70.md`, and this active
  registry.  The first paper now attributes the relocated calculus correctly;
  the new frontier article has an explicit formalization boundary and its
  formerly missing, visually inspected PDF.

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

Each substantive non-merge checkpoint message records its exact textual
validation and any deferred Lean targets.  Incoming commits `b164f3d2f` and
`c62a56d95` report focused and aggregate validation of the core inverse
calculus and smoothness, while the other incoming mathematical lanes likewise
carry focused immutable evidence.  Those reports predate the current-only
translated-polynomial batch and do not validate the exact combined
`4b8c0094e + 783cecf720` tree.

## Current merge-checkpoint evidence

For the exact source-resolved `4b8c0094e + 783cecf720` tree, the 13 incoming
Lean files all retain `set_option autoImplicit false`.  The tree-wide forbidden
declaration/placeholder scan, conflict-marker scan, and `git diff --check` are
clean.  The documentation ratchet passes with 188 modules, 3,149 public
declarations, 159 existing missing comments in 17 files, and no missing module
headers.

Both semantically updated papers were built with three successful PDFLaTeX
passes and inspected as rendered pages.  The non-elementarity paper is 13 A4
pages with PDF SHA-256
`85039AE2C54C6B595338713BB19026C3FB470A28E5F56EB088712219A26F8F79`.
The new dyadic/q-connections frontier paper is 23 A4 pages with PDF SHA-256
`A642AA471132A4A6AFEFF997D172AF75E946D1A794029C6E6F4C0B36F4D88FD0`;
its 94 labels have no case-sensitive duplicates and all 80 references resolve.
This is static and document-build evidence only.  No Lean build has yet been
run on the exact combined tree.

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
gate passed.  The third pinned integration at `783cecf720` is source-resolved
over published checkpoint `4b8c0094e`; active ownership is unchanged, and
focused Lean validation of the exact combined tree remains pending until this
merge is published and the now-free host-wide build lane is rechecked and
claimed.
