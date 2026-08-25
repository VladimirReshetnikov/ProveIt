# Workstream registry: `claude/fabius-non-elementary-proof-861d70`

**Status: closed historical record.** The advertised work is integrated into
mainline through the pinned synchronization tip `5ed2fc27b`; this file was last
classified on 2026-08-25 and grants no live source or build lease.

This file implements the per-branch registry fallback proposed in
[`../COLLABORATION.md`](../COLLABORATION.md) ("one small file per branch,
`docs/registry/<branch>.md`").

```text
SYNC Fabius
worktree/task: fabius-non-elementary-proof-861d70 — the Fabius function on
  (0,1) is not an elementary function
branch/base: claude/fabius-non-elementary-proof-861d70, based on
  origin/main at 26b8b2e54
git owner / build owner: self / self (own worktree, own `.lake`)
```

## Write set

New files only, plus registration and README lines.

- `Lean/FabiusFunction/ElementaryFunction.lean` — the class of elementary
  functions of one real variable and the density of its analytic locus.
  Depends on `Mathlib` only; no Fabius import.
- `Lean/FabiusFunction/NotElementary.lean` — the combination with
  `NowhereAnalytic`.
- `Lean/FabiusFunction.lean` — two registration lines.
- `docs/Non_Elementarity_of_the_Fabius_Function/` — `.tex` and committed
  `.pdf`.
- `docs/registry/claude-fabius-non-elementary-proof-861d70.md` (this file).
- `README.md` — the new document's entry and one focused-import row.

## Read-only

The whole directory.  In particular this branch depends on, and does not
write, `NowhereAnalytic.lean`, `OriginalPaperSupplement.lean`,
`PaperStatements.lean` and `Basic.lean`.  No existing public name is moved or
renamed.

## Result

`Fabius.canonical_fabius_not_isElementary_on_Ioo`: there is no elementary
`g : ℝ → ℝ` with `Set.EqOn g (fabiusReal fabius) (Set.Ioo 0 1)`.  More
generally `Fabius.not_isElementary_eqOn` rules out agreement on *any* nonempty
open subset of `[0,1]`, and the same holds for `rvachevUp` on `[-1,1]` and for
`extendedFabius` on `[0,2)`.

The mathematical input from this branch is
`Fabius.IsElementary.dense_analyticLocus`: the analytic locus of an elementary
function is dense (and open, by `Fabius.isOpen_analyticLocus`).  The nowhere
analyticity is taken unchanged from `NowhereAnalytic.lean`.

## Build ownership

This worktree has its own `.lake` whose `packages` is a directory junction to
the shared `C:\ProveIt\.lake\packages`.  Builds are strictly serialized, one
`lake build +<module>` per invocation, `LAKE_JOBS=1`, in topological order.

`ElementaryFunction.lean` is the cheap module to iterate on: its import
closure is `Mathlib` only, so it rebuilds in well under a minute off a warm
`Mathlib`.  `NotElementary.lean` costs the whole 27-module closure of
`NowhereAnalytic`.

## Not claimed

The class is closed under `n`-th roots, but has no constructor for a general
algebraic function — a continuous branch of `P(x, y) = 0` with elementary
coefficients and non-solvable Galois group.  Wikipedia's definition speaks of
"roots", which `IsElementary.rpow` provides; Liouville's differential-field
definition is wider.  Extending to it needs an analytic implicit function
theorem over `ℝ`, which `Mathlib` does not currently provide.
