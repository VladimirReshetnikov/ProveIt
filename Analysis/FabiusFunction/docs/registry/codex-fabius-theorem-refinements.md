# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at
  ad6cf6a079d551908ae5ef7431b994899ec9b8d7 after the first pinned integration,
  with the second pinned origin/main tip source-resolved for this merge
  639bfc53e205c6e09d62ece6c458876d5fffc0f9
git owner: root in this worktree
build owner: not held; the external non-elementarity worktree at immutable
  475a4f27b24206c895758c0fcb47e9d3055a0e06 owns a guarded 35-module
  serialized closure build.  Its launcher is bash 29408 -> 30280, its stable
  driver is sh 35084 with MSYS lock PID 289364, and at the 2026-08-25 11:29:08
  -07:00 snapshot its current child chain was sh 8180 -> lake 21064 -> lake
  7292 -> lean 14712 for +FabiusFunction.FabiusInverse.  Arithmetic through
  DyadicAnalytic had passed.  A read-only 11:31:13 -07:00 check found the same
  closure still active and advanced to +FabiusFunction.GlobalExtension;
  ownership lasts until the driver records a terminal event or the owner
  reports a handoff
source lease: refreshed 2026-08-25 11:29 -07:00 through 11:59 -07:00
next synchronization checkpoint: commit and push the semantically resolved
  six-conflict merge and its regenerated, inspected TeX/PDF pair; then wait
  for the external terminal event and obtain the lane for the exact
  combined-tree focused Lean build
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
- Second integration lease for pinned main `639bfc53e` over `ad6cf6a07`:
  `Lean/FabiusFunction/InverseBranch.lean`,
  `Lean/FabiusFunction/InverseNotElementary.lean`,
  `docs/Non_Elementarity_of_the_Fabius_Function/Non_Elementarity_of_the_Fabius_Function.tex`,
  its paired `.pdf`, `docs/PAPER_COVERAGE.md`, and
  `docs/registry/claude-fabius-non-elementary-proof-861d70.md`.  The six
  conflicts were resolved semantically as one inverse-branch cluster,
  retaining the `analyticAt_of_rightInverse` naming, the local
  `AnalyticDenseOn` API, and the
  unconditional interior derivative theorem for `fabiusInv`.  The
  `IsElementaryOrInverse.invBranch` and conditional Lambert-`W` APIs require
  continuity on the open inverse domain and analyticity only on
  `interior Uᶜ`, not at every point outside `U`; in particular the branch
  boundary is deliberately excluded.  The TeX, coverage map, rebuilt PDF, and
  peer registry now state exactly those hypotheses rather than preserving
  either side's stale prose.

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

Each substantive non-merge checkpoint message records its exact textual
validation and any deferred Lean targets.  The live external closure build is
for the clean non-elementarity worktree at `475a4f27b`; it does not validate
this manually reconciled second integration.  Focused compilation of the
translated-polynomial slice and the exact combined
`ad6cf6a07 + 639bfc53e` tree remains pending until the external host-wide
build lease reaches a terminal event and this merge has an immutable tip.

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
gate passed.  The second pinned integration at `639bfc53e` has been
source-resolved over `ad6cf6a07`; active ownership is unchanged, and focused
Lean validation of the exact combined tree remains pending behind the
external host-wide build owner.
