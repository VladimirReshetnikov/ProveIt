# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at
  a95bd19137c75dba867e0a17019036c0ea6d77fc before merging pinned origin/main
  1e371c773b387a7635fd28452512ab9eb6831abb
git owner: root in this worktree
build owner: not held; the external non-elementarity worktree owns target
  +FabiusFunction.NowhereAnalytic, process tree 31176 -> 5816 -> 36672, as
  observed at 2026-08-25 11:08 -07:00, as part of its serialized closure build
  and until the owner reports a terminal event or handoff
source lease: refreshed 2026-08-25 11:08 -07:00 through 11:38 -07:00
next synchronization checkpoint: finish the semantic resolution of the pinned
  main merge, regenerate and inspect its conflicted TeX/PDF pair, commit and
  push; then obtain the build lane for the combined-tree focused Lean build
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
- Integration lease for pinned main `1e371c773`: `README.md`,
  `Lean/FabiusFunction/InverseBranch.lean`,
  `Lean/FabiusFunction/InverseNotElementary.lean`,
  `docs/Non_Elementarity_of_the_Fabius_Function/Non_Elementarity_of_the_Fabius_Function.tex`,
  its paired `.pdf`, and
  `docs/registry/claude-fabius-non-elementary-proof-861d70.md`.  Resolve the
  document/registry conflicts semantically and correct the newly discovered
  unconditional Lambert-`W` prose; the Lean theorem itself is conditional on
  continuity on an open inverse domain and analyticity at every point outside
  that domain.

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

Each substantive non-merge checkpoint message records its exact textual
validation and any deferred Lean targets.  Focused compilation of the formerly
branch-only Lean slices remains pending until the external host-wide build
lease is released; mainline has since absorbed the same source changes, so
validation must run on the new combined immutable tip rather than on a stale
pre-merge tree.

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
gate passed.  The exact combined tree is still being resolved, and its focused
Lean build remains pending behind the external host-wide build owner.
