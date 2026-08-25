# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at da7d0c3a3 before merging
  pinned origin/main 436e421f133ce637063fe460d7c92459a8016bed
git owner: root in this worktree
build owner: not held; another worktree currently owns the host-wide Lean lane
source lease: 2026-08-25 09:29 -07:00 through 09:59 -07:00
next synchronization checkpoint: after this pinned-main merge is committed and
  pushed, then before theorem edits if a fetched branch overlaps the translated
  polynomial declaration family
```

## Current write lease

- `Lean/FabiusFunction/FabiusQBinomialTaylor.lean`: audit and, if the exact
  all-index statements survive review, expose the coefficients, zero
  criterion, and natural degree of
  `thueMorseTranslatedPowerSumPolynomial`.
- `docs/registry/codex-fabius-theorem-refinements.md`: this status record.

The integration lease on `README.md`, `docs/COLLABORATION.md`,
`docs/PAPER_COVERAGE.md`, and their paired mathematical documents ends when the
pinned-main merge is reviewed, committed, and pushed.

## Read-only survey

- `ThueMorsePrefix.lean`, `ThueMorseExponential.lean`,
  `ThueMorseGenerating.lean`, and `FabiusUniformSpline.lean` for existing
  sharp-moment and real-scalar APIs;
- `ProbabilityLaplaceMoments.lean`, `FabiusComplexMGF.lean`, and their callers
  to avoid reintroducing transform bridges already integrated upstream; and
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

Each commit message records its exact textual validation and any deferred Lean
targets.  Focused compilation of the formerly branch-only Lean slices remains
pending until the external host-wide build lease is released; mainline has
since absorbed the same source changes, so validation must run on the new
combined immutable tip rather than on a stale pre-merge tree.

## Proposed translated-polynomial API

The current candidate is intentionally provisional until independent review:

- an exact coefficient formula in terms of
  `thueMorseCenteredPowerSum k (d - j)`;
- vanishing exactly when `d < k`; and
- the all-index degree drop `natDegree = d - k`, including Lean's zero
  polynomial convention in the `d < k` case.

Boundary cases `k = 0`, `d < k`, `d = k`, and the nonzero leading coefficient
must all be checked before editing.  No synonym should be added if current
mainline already exposes an equivalent result under another name.
