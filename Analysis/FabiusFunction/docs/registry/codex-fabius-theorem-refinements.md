# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at 09885a710 before merging
  pinned origin/main 5ed2fc27b0844bcb07db0b4a4e2ae008e8086947
git owner: root in this worktree
build owner: not held; another worktree currently owns the host-wide Lean lane
source lease: 2026-08-25 08:10 -07:00 through 08:40 -07:00
next synchronization checkpoint: after the translated-polynomial batch, or
  immediately if a fetched branch overlaps its declaration family
```

## Current write lease

- `Lean/FabiusFunction/FabiusQBinomialTaylor.lean`: audit and, if the exact
  all-index statements survive review, expose the coefficients, zero
  criterion, and natural degree of
  `thueMorseTranslatedPowerSumPolynomial`.
- `docs/registry/codex-fabius-theorem-refinements.md`: this status record.

The merge-resolution lease on `AGENTS.md`, `README.md`,
`docs/COLLABORATION.md`, and `docs/PAPER_COVERAGE.md` ends when the pinned-main
merge is reviewed, committed, and pushed.

## Read-only survey

- `ThueMorsePrefix.lean`, `ThueMorseExponential.lean`,
  `ThueMorseGenerating.lean`, and `FabiusUniformSpline.lean` for existing
  sharp-moment and real-scalar APIs;
- the negative-Laplace vertical, logarithmic, Bromwich, and saddle callers for
  a next nonduplicate transform lemma; and
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
