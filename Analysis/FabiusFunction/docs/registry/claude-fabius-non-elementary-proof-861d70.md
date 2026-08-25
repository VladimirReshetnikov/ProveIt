# Workstream registry: `claude/fabius-non-elementary-proof-861d70`

This file implements the per-branch registry fallback proposed in
[`../COLLABORATION.md`](../COLLABORATION.md) ("one small file per branch,
`docs/registry/<branch>.md`").  A tracked file is the only channel that
provably reaches every worktree, including the two `codex/*` workstreams
running on a different machine.

```text
SYNC Fabius
worktree/task: fabius-non-elementary-proof-861d70 — the Fabius function on
  (0,1) is not an elementary function
branch/base: claude/fabius-non-elementary-proof-861d70, fast-forwarded onto
  origin/main at 5437f9d0c (which already contains this branch's first two
  commits, merged upstream by the integrator)
git owner / build owner: self / self (own worktree, own `.lake`)
```

## Write set

New files, plus registration and README lines.  No existing Lean module is
edited; no existing public name is moved or renamed.

- `Lean/FabiusFunction/ElementaryFunction.lean` — the class of elementary
  functions of one real variable and the density of its analytic locus.
  Depends on `Mathlib` only; no Fabius import, so it is cheap to rebuild.
- `Lean/FabiusFunction/NotElementary.lean` — the combination with
  `NowhereAnalytic`.
- `Lean/FabiusFunction/AlgebraicBranch.lean` — *in progress*, see below.
- `Lean/FabiusFunction.lean` — registration lines only.
- `docs/Non_Elementarity_of_the_Fabius_Function/` — `.tex` and committed
  `.pdf`.
- `docs/registry/claude-fabius-non-elementary-proof-861d70.md` (this file).
- `README.md` — the new document's entry and one focused-import row.

## Read-only

The whole directory.  In particular this branch depends on, and does not
write, `NowhereAnalytic.lean`, `OriginalPaperSupplement.lean`,
`PaperStatements.lean`, `Basic.lean`, `Differential.lean` and `Arithmetic.lean`.

If a `codex/*` workstream needs to move or rename anything in
`NowhereAnalytic.lean` — specifically `fabius_not_analyticAt`,
`rvachev_not_analyticAt`, `extendedFabius_not_analyticAt`,
`canonical_fabius_not_analyticAt`, `canonical_fabius_analyticAt_iff` — please
say so here first; `NotElementary.lean` consumes exactly those five names and
nothing else from that module.

## Result

`Fabius.canonical_fabius_not_isElementary_on_Ioo`: there is no elementary
`g : ℝ → ℝ` with `Set.EqOn g (fabiusReal fabius) (Set.Ioo 0 1)`.  More
generally `Fabius.not_isElementary_eqOn` rules out agreement on *any* nonempty
open subset of `[0,1]`, and the same holds for `rvachevUp` on `[-1,1]` and for
`extendedFabius` on `[0,2)`.

The mathematical input from this branch is
`Fabius.IsElementary.dense_analyticLocus`: the analytic locus of an elementary
function is dense, and open by `Fabius.isOpen_analyticLocus`.  Nowhere
analyticity is taken unchanged from `NowhereAnalytic.lean`.

## In progress

`AlgebraicBranch.lean` proves that a continuous branch of a polynomial
equation with real-analytic coefficients and nowhere-vanishing leading
coefficient is analytic on a dense subset, by a degree induction that avoids
the discriminant (`Mathlib` has no `Separable`/`discr` bridge and no
continuity of roots).  It rests on `ContDiffAt.implicitFunction`, which
`Mathlib` states at every exponent in `ℕ ∪ {∞, ω}`, so instantiating at `ω`
gives an analytic implicit function theorem.

Its purpose is to add one constructor to `IsElementary`, widening the class
from "closed under `n`-th roots" (Wikipedia's formulation) to "closed under
arbitrary algebraic functions" (Liouville's).  This is a strengthening beyond
the task's stated scope, and the main result does not depend on it: if it does
not land, `ElementaryFunction.lean` and `NotElementary.lean` stand unchanged.
It will not be committed until it compiles.

## Build ownership

This worktree has its own `.lake` whose `packages` is a directory junction to
the shared `C:\ProveIt\.lake\packages`.  Builds are strictly serialized, one
`lake build +<module>` per invocation, `LAKE_JOBS=1`, in topological order —
`order.txt` at the repository root of this worktree holds the current list.
Only one `lean` process runs at a time on this machine; a second one makes the
13 GB box thrash and produces the misleading `failed to read file '….olean'`.

`ElementaryFunction.lean` is the cheap module to iterate on: `Mathlib`-only
imports, about seventy seconds off a warm `Mathlib`.  `NotElementary.lean`
costs the whole 28-module closure of `NowhereAnalytic`.

## Not claimed

Until `AlgebraicBranch.lean` lands, the class has no constructor for a general
algebraic function — a continuous branch of `P(x, y) = 0` with elementary
coefficients and non-solvable Galois group.

Two further caveats, both recorded in the write-up:

- The unrestricted two-variable power `f ^ g` is not a constructor, because
  `Mathlib`'s `Real.rpow` is sign-dependent at a negative base.
  `IsElementary.rpow_of_pos` covers every positive base.
- `IsElementary.rpow` gives `n`-th roots only on `[0, ∞)`, since
  `(-8 : ℝ) ^ (1/3 : ℝ) = 1`.  The classical odd root is in the class by the
  separate derivation `IsElementary.signedRpow`, verified by
  `Fabius.signedRoot_pow`.
