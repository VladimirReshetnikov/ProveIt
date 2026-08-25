# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at
  8cc000b11d1f5426d9b56d1bff22538fdd8bcc49, containing pinned origin/main
  5e80805b1ee92697723949d125aa0d6dbf32f538
git owner: root in this worktree
build owner: not held; the external non-elementarity worktree owns target
  +FabiusFunction.SharpFlatness, process tree 28952 -> 30068 -> 16336, as part
  of its serialized closure build and until the owner reports a handoff
source lease: 2026-08-25 10:16 -07:00 through 10:46 -07:00
next synchronization checkpoint: publish the independently reviewed but
  explicitly uncompiled translated-polynomial source checkpoint; then obtain
  the build lane, compile the focused module, and re-fetch origin/main before
  any validated integration checkpoint
```

## Current write lease

- `Lean/FabiusFunction/FabiusQBinomialTaylor.lean`: audit and, if the exact
  all-index statements survive implementation review, expose the coefficient
  formula, exact zero criterion, natural degree, degree, leading coefficient,
  and useful boundary normal forms of
  `thueMorseTranslatedPowerSumPolynomial`; also remove redundant `CharZero`
  binders already implied by `Algebra ℚ K`.
- `README.md`: document the exact structure of the inner translated polynomial.
- `docs/AUDIT_FINDINGS.md`: close the verified redundant-`CharZero` API
  finding.
- `docs/COLLABORATION.md`: retire the translated-polynomial candidate once the
  theorem batch is compiled and published.
- `docs/registry/codex-fabius-theorem-refinements.md`: this status record.

## Read-only survey

- `ThueMorsePrefix.lean`, `ThueMorseExponential.lean`,
  `ThueMorseGenerating.lean`, and `FabiusUniformSpline.lean` for existing
  sharp-moment and real-scalar APIs;
- `ProbabilityLaplaceMoments.lean`, `FabiusComplexMGF.lean`, and their callers
  to avoid reintroducing transform bridges already integrated upstream; and
- `AlgebraicBranch.lean` and `NotElementary.lean`, whose completed localized
  algebraic-branch obstruction is integrated at pinned main `3de52ca1c`, to
  avoid duplicating that theorem family; and
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
- `3de52ca1c` on mainline completes and registers the localized
  algebraic-branch obstruction, including the direct nowhere-analytic
  corollaries, so that formerly advertised work is no longer an open lane.
- `5e80805b1` on mainline integrates the foundational/Fourier/probability and
  finite-remainder generalizations.  In particular `cfc70e3bc` factors the
  q-binomial refinement coefficient argument by degree without consuming the
  separate translated-polynomial coefficient/zero/degree lane leased here.

Each commit message records its exact textual validation and any deferred Lean
targets.  Focused compilation of the formerly branch-only Lean slices remains
pending until the external host-wide build lease is released; mainline has
since absorbed the same source changes, so validation must run on the new
combined immutable tip rather than on a stale pre-merge tree.

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
`git diff --check`, the forbidden-placeholder/conflict-marker scans, and the
documentation baseline gate pass; the focused Lean build remains pending
behind the external host-wide build owner.
