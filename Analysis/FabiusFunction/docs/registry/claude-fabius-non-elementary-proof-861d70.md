# Workstream registry: `claude/fabius-non-elementary-proof-861d70`

This file implements the per-branch registry fallback proposed in
[`../COLLABORATION.md`](../COLLABORATION.md) ("one small file per branch,
`docs/registry/<branch>.md`").  A tracked file is the only channel that
provably reaches every worktree, including the two `codex/*` workstreams
running on a different machine.

```text
SYNC Fabius
worktree/task: fabius-non-elementary-proof-861d70 — neither the Fabius
  function nor its inverse is elementary on (0,1), and neither is reachable
  once inverse branches (Lambert W included) are adjoined
branch/base: claude/fabius-non-elementary-proof-861d70, merged with
  origin/main at cb54665bf.  No conflicts.  The codex refactoring of
  `analyticDenseOn_of_isElementary_coeffs` came in with that merge and is kept
  as it arrived.
git owner / build owner: self / self (own worktree, own `.lake`)
status: complete and verified — 35-module closure builds clean, every exported
  theorem audited for axioms, write-up and PDF current
```

## Write set

New files, plus registration and README lines.  No existing Lean module is
edited; no existing public name is moved or renamed.

- `Lean/FabiusFunction/ElementaryFunction.lean` — the class of elementary
  functions of one real variable and the density of its analytic locus.
  Depends on `Mathlib` only; no Fabius import, so it is cheap to rebuild.
- `Lean/FabiusFunction/NotElementary.lean` — the combination with
  `NowhereAnalytic`.
- `Lean/FabiusFunction/AlgebraicBranch.lean` — continuous branches of
  polynomial equations with analytic coefficients.
- `Lean/FabiusFunction/InverseBranch.lean` — the analytic inverse function
  theorem, and the class closed under inverse branches.
- `Lean/FabiusFunction/InverseNotElementary.lean` — the inverse Fabius
  function, and the strengthened non-representability theorems.
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
generally `Fabius.not_isElementary_eqOn_of_interior_nonempty` rules out
agreement on *any* subset of `[0,1]` with nonempty interior — that
generalization came from a `codex/*` workstream and is kept — and the same
holds for `rvachevUp` on `[-1,1]` and for `extendedFabius` on `[0,2)`.

All 98 theorems exported by the five new modules — `ElementaryFunction`,
`AlgebraicBranch`, `NotElementary`, `InverseBranch`, `InverseNotElementary` —
have axiom set `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`
anywhere, and so do the five inverse-calculus theorems this workstream
contributed to `FabiusInverse.lean` (`fabiusInv_mem_Ioo`,
`fabiusInv_hasDerivAt`, `deriv_fabiusInv`, `deriv_fabiusInv_pos`,
`deriv_fabiusInv_eq_inv_two_mul_rvachevUp`).  The count fell from 100 to 98
because two of them moved out of `InverseNotElementary.lean` in that
upstreaming, not because anything was dropped.  The audit is a generated `#print axioms` sweep over every
`theorem`/`lemma` at any namespace depth in those files, run against the fully
built closure; it is re-run after every change to them.

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

Every hypothesis on the branch is confined to the region `U`.  That is not
cosmetic: a version with global hypotheses excludes `y ^ 5 - y - x = 0`
altogether, since a global continuous solution would be a continuous right
inverse of `w ↦ w ^ 5 - w`, and that polynomial has none — it is monotone only
on three pieces, and the image of each is a proper subinterval of `ℝ`.  That
equation is the standard example of a non-solvable Galois group.  An
adversarial review caught the earlier global form claiming coverage it did not
have; the theorem was strengthened rather than the claim weakened.

A `codex/*` workstream then factored the localized proof, and the refactoring
is kept as it arrived: `analyticDenseOn_of_isElementary_coeffs` now carries the
content, with `analyticDenseOn_of_inter_open_dense` isolating the step that
removes the restriction to the coefficients' common analytic locus, and
`AnalyticDenseOn.not_eqOn_of_forall_not_analyticAt` isolating the germ-transport
step.  `exists_analyticAt_of_isElementary_coeffs`,
`dense_analyticLocus_of_isElementary_coeffs` and `not_algebraicBranch_eqOn`
keep their statements and are now one-liners over it.  Nothing downstream in
`InverseBranch` or `InverseNotElementary` needed changing.

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
`lake build +<module>` per invocation, `LAKE_JOBS=1`, in topological order.
When useful, `order.txt` and `build_closure.sh` may be created at the repository
root as ignored, machine-local build drivers; they are not tracked project
files.
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

## Inverses

`InverseBranch.lean` observes that a left inverse is an implicit branch of the
simplest possible equation — `h (g x) = x` says `g` is a continuous branch of
`h z - x = 0` — so `Fabius.analyticAt_of_rightInverse`, the analytic inverse
function theorem, is `analyticAt_of_continuous_branch` applied with no further
analysis.  On top of it, `Fabius.exists_analyticAt_of_rightInverse`: a
continuous right inverse of a densely analytic function is analytic somewhere.

A `codex/*` workstream added the relative form
`Fabius.analyticDenseOn_of_rightInverse` — the same conclusion tested on every
nonempty open subset of a branch domain that need not itself be open — together
with `Fabius.not_eqOn_fabiusInv_of_analyticDenseOn`, which weakens the
hypothesis of the obstruction from a globally dense analytic locus to relative
density in `interior U`.  Both arrived by merge and are kept;
`not_eqOn_fabiusInv_of_dense_analyticLocus` is now a corollary of the second.

`Fabius.IsElementaryOrInverse` closes the elementary functions under
continuous inverse branches at any depth, and
`IsElementaryOrInverse.dense_analyticLocus` shows the enlarged class is still
densely analytic.  Its constructor is localized to an open `U` because Lambert
`W` satisfies its identity only on `[-1/e, ∞)`;
`Fabius.isElementaryOrInverse_of_lambertW` records the membership for an
arbitrary branch, since `Mathlib` does not define `W`.  The constructor's
analyticity clause is `∀ y ∈ interior Uᶜ`, not `∀ y ∉ U`: the branch point
`-1/e` lies on the boundary of `W`'s natural `U`, and demanding analyticity
there would make the `W` instance vacuous.  That clause constrains the chosen
extension of the branch past `U` rather than following from `Mathlib`'s junk
values; constant extension always satisfies it, and `U = ∅` degenerates it to
"`g` is entire".

`InverseNotElementary.lean` applies this to `fabiusInv`:
`fabiusInv_not_analyticAt` and `fabiusInv_analyticAt_iff` pin the analytic
locus of the inverse to `ℝ \ [0,1]`, exactly as for `F`.  In the interior the
argument is the inverse function theorem run backwards, and the one thing to
check is that `F⁻¹` has no critical point.  That is `deriv_fabiusInv_ne_zero`,
now a one-liner over `deriv_fabiusInv_pos`.  The chain is
`deriv_fabiusReal_pos` gives `F' > 0` on `(0,1)`, so
`HasDerivAt.of_local_left_inverse` supplies `(F⁻¹)' = 1 / F' > 0` there.

That derivative calculus started here as `hasDerivAt_fabiusInv`; a `codex/*`
workstream upstreamed it into `FabiusInverse.lean` as `fabiusInv_hasDerivAt`,
`deriv_fabiusInv`, `deriv_fabiusInv_eq_inv_two_mul_rvachevUp` and
`deriv_fabiusInv_pos`, which is the better home for it, and that placement is
kept.  `fabiusInv_mem_Ioo` moved with it.  The original spelling
`hasDerivAt_fabiusInv` still exists, deliberately, as a compatibility alias in
that file; docstrings here cite `deriv_fabiusInv_pos` because it is the
primary name, not because the alias was broken.

Every ``Fabius.*`` name appearing in a docstring of the five modules — thirty
of them — is checked to resolve, by a generated `#check` sweep run against the
built closure.  Prose citations are otherwise invisible to the compiler.

`F'` now enters the five modules of this workstream only through the imported
`deriv_fabiusInv_pos`.  It is *not* true that this is the only use of a
differential property of `F` — `fabius_differentiable` appears once more, in
`fabiusInv_not_analyticAt`, to produce a `ContinuousAt` for the inverse
function theorem.  The checkable statement is the one about `F'`.

An earlier version derived this by differentiating `F⁻¹ ∘ F = id`, which needs
`F⁻¹` to be differentiable and so carried an `AnalyticAt ℝ (fabiusInv F hF) y`
hypothesis — refuted, for every `y ∈ Icc 0 1`, by `fabiusInv_not_analyticAt`
twelve lines below.  The statement was therefore vacuous.  An adversarial
review caught it; the fix strengthens the theorem rather than the wording.

`Fabius.not_eqOn_of_dense_analyticLocus` now states the obstruction once, with
density as the entire hypothesis; `IsElementary.not_eqOn_of_interior_nonempty`
(from a `codex/*` workstream) is a one-line corollary of it, and every
non-representability theorem here is that lemma applied to a class for which
density has been proved.

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
