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

## Algebraic branches

`AlgebraicBranch.lean` proves that a continuous branch of a polynomial
equation with real-analytic coefficients and nowhere-vanishing leading
coefficient is analytic on a dense subset, by a degree induction that avoids
the discriminant (`Mathlib` has no `Separable`/`discr` bridge and no
continuity of roots).  It rests on `ContDiffAt.implicitFunction`, which
`Mathlib` states at every exponent in `ℕ ∪ {∞, ω}`, so instantiating at `ω`
gives an analytic implicit function theorem — packaged here as
`Fabius.analyticAt_implicitFunction`.

`Fabius.not_algebraicBranch_eqOn` then draws the non-elementarity conclusion
for such branches, covering the algebraic functions that are not expressible
by radicals.

This deliberately does *not* add a constructor to `IsElementary`.  Doing so
would cost `IsElementary.comp`: composing an algebraic branch with an
elementary function yields a branch over the composed coefficients, but a
*continuous* one only if the inner function is continuous, and elementary
functions need not be.  Rather than weaken the closure theorem, the analytic
statement is proved separately and the two are combined at the point of use.

**Status: compiled, registered in `Lean/FabiusFunction.lean`, axiom set
`[propext, Classical.choice, Quot.sound]`.**

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

## One directory-wide observation, not acted on beyond this document

The shared preamble declares every theorem-like environment on the `theorem`
counter (`\newtheorem{lemma}[theorem]{Lemma}` and so on).  `cleveref` takes a
reference's *name* from its counter, not its environment, so `\Cref` to a
lemma, definition, corollary, proposition or warning prints "Theorem".  The
headings are right; only the cross-references are wrong.  In
`Fabius_Function_and_Rvachev_Up.tex` this affects 127 `\Cref` uses against
`lem:`, `cor:` and `def:` labels.

I did not touch the shared preamble, since `AGENTS.md` asks for it verbatim.
In `Non_Elementarity_of_the_Fabius_Function.tex` the references to
non-theorem environments are written as `Lemma~\ref{...}` and so on, which is
a body-level change only.  The global fix, if anyone wants it, is the
`aliascnt` package — `\newaliascnt{lemma}{theorem}` plus
`\aliascntresetthe{lemma}` and `\crefname{lemma}{Lemma}{Lemmas}` — and it
would have to be applied to the preamble of every document at once.

## Not claimed

A tower that *interleaves* algebraic extensions with exponentials and
logarithms at several levels is covered only when it can be presented either
as a member of `IsElementary` or as a single algebraic step over elementary
coefficients.  Closing that would need the fact that a nonconstant real
analytic function on an interval has image containing an interval, so that
preimages of dense open sets stay dense; classical, and not formalized here.

Two further caveats, both recorded in the write-up:

- The unrestricted two-variable power `f ^ g` is not a constructor, because
  `Mathlib`'s `Real.rpow` is sign-dependent at a negative base.
  `IsElementary.rpow_of_pos` covers every positive base.
- `IsElementary.rpow` gives `n`-th roots only on `[0, ∞)`, since
  `(-8 : ℝ) ^ (1/3 : ℝ) = 1`.  The classical odd root is in the class by the
  separate derivation `IsElementary.signedRpow`, verified by
  `Fabius.signedRoot_pow`.
