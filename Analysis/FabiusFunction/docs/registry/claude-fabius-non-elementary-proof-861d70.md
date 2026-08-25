# Workstream registry: `claude/fabius-non-elementary-proof-861d70`

**Status: closed historical source record; exact combined-tree validation
pending.** The elementary/algebraic work and its later inverse extension are
integrated through pinned `origin/main` at
`783cecf7208edd4de86fd0cee7d4b9f13299ee60`.  This file grants no
live source or build lease.  All validation statements below are reports tied
to immutable historical commits, not evidence for the manually resolved
combined tree.  The normal lease and build-terminal-event rules in
[`../COLLABORATION.md`](../COLLABORATION.md) govern any future source work.

This file is the per-branch registry fallback proposed in
[`../COLLABORATION.md`](../COLLABORATION.md) ("one small file per branch,
`docs/registry/<branch>.md`").  At its creation, a tracked file was the channel
used to reach every worktree, including two `codex/*` workstreams on another
machine.

```text
HISTORICAL SYNC Fabius
worktree/task: fabius-non-elementary-proof-861d70 — elementary, algebraic-
  branch, inverse-branch, and inverse-Fabius non-representability
integration pin: pinned origin/main at
  783cecf7208edd4de86fd0cee7d4b9f13299ee60
source/build owner: none granted by this closed record
validation: immutable reported evidence is recorded below; exact combined-tree
  validation remains pending
```

## Write set

This workstream wrote the listed files, plus its registration and README lines.
It did not move or rename existing public names outside this set.

- `Lean/FabiusFunction/ElementaryFunction.lean` — the class of elementary
  functions of one real variable and the density of its analytic locus.
  Depends on `Mathlib` only; no Fabius import, so it is cheap to rebuild.
- `Lean/FabiusFunction/NotElementary.lean` — the combination with
  `NowhereAnalytic`.
- `Lean/FabiusFunction/AlgebraicBranch.lean` — compiled and registered;
  continuous branches of polynomial equations with analytic coefficients.
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

The implementation depended on exactly five names from `NowhereAnalytic.lean`:
`fabius_not_analyticAt`, `rvachev_not_analyticAt`,
`extendedFabius_not_analyticAt`, `canonical_fabius_not_analyticAt`, and
`canonical_fabius_analyticAt_iff`.  This records the historical dependency
boundary; future changes follow the current registry and lease rules.

## Result

`Fabius.canonical_fabius_not_isElementary_on_Ioo`: there is no elementary
`g : ℝ → ℝ` with `Set.EqOn g (fabiusReal fabius) (Set.Ioo 0 1)`.  More
generally `Fabius.not_isElementary_eqOn_of_interior_nonempty` rules out
agreement on *any* subset of `[0,1]` with nonempty interior — that
generalization came from a `codex/*` workstream and is kept — and the same
holds for `rvachevUp` on `[-1,1]` and for `extendedFabius` on `[0,2)`.

At its then-immutable source state, the earlier elementary/algebraic batch was
reported to have eighteen exported theorems with axiom set
`[propext, Classical.choice, Quot.sound]`.  The later five-module closure
evidence is recorded below with its exact source commits.  Neither report is
validation of the exact combined post-merge tree.

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
altogether, since `w ↦ w ^ 5 - w` is not injective and so no continuous branch
on all of `ℝ` exists — and that equation is the standard example of a
non-solvable Galois group.  An adversarial review caught the earlier global
form claiming coverage it did not have; the theorem was strengthened rather
than the claim weakened.

This deliberately does *not* add a constructor to `IsElementary`.  Doing so
would cost `IsElementary.comp`: composing an algebraic branch with an
elementary function yields a branch over the composed coefficients, but a
*continuous* one only if the inner function is continuous, and elementary
functions need not be.  Rather than weaken the closure theorem, the analytic
statement is proved separately and the two are combined at the point of use.

**Status: compiled, registered in `Lean/FabiusFunction.lean`, axiom set
`[propext, Classical.choice, Quot.sound]`.**

## Historical build ownership

The following records the originating worktree's build setup; it is not a live
lease.

The originating worktree had its own `.lake` whose `packages` was a directory
junction to the shared `C:\ProveIt\.lake\packages`.  Builds were strictly
serialized, one `lake build +<module>` per invocation, `LAKE_JOBS=1`, in
topological order.  When useful, `order.txt` and `build_closure.sh` could be
created at the repository root as ignored, machine-local build drivers; they
were not tracked project files.  The originating 13 GB machine ran only one
`lean` process at a time; a second made it thrash and produced the misleading
`failed to read file '….olean'`.

`ElementaryFunction.lean` is the cheap module to iterate on: `Mathlib`-only
imports, about seventy seconds off a warm `Mathlib`.  `NotElementary.lean`
costs the whole 28-module closure of `NowhereAnalytic`.

## One directory-wide observation, not acted on beyond this document

The shared preamble declares every theorem-like environment on the `theorem`
counter (`\newtheorem{lemma}[theorem]{Lemma}` and so on).  `cleveref` takes a
reference's *name* from its counter, not its environment, so `\Cref` to a
lemma, definition, corollary, proposition or warning prints "Theorem".  The
headings are right; only the cross-references are wrong.  This remains a
qualitative directory-wide issue; exact occurrence counts are document-version
dependent and the earlier recorded count is now stale.

I did not touch the shared preamble, since `AGENTS.md` asks for it verbatim.
In `Non_Elementarity_of_the_Fabius_Function.tex` the references to
non-theorem environments are written as `Lemma~\ref{...}` and so on, which is
a body-level change only.  The global fix, if anyone wants it, is the
`aliascnt` package — `\newaliascnt{lemma}{theorem}` plus
`\aliascntresetthe{lemma}` and `\crefname{lemma}{Lemma}{Lemmas}` — and it
would have to be applied to the preamble of every document at once.

## Inverses

`InverseBranch.lean` observes that a right inverse is an implicit branch of the
simplest possible equation — `h (g x) = x` says that `h` is a left inverse of
`g`, equivalently that `g` is a continuous right inverse of `h`, and makes `g`
a branch of `h z - x = 0`.  Thus `Fabius.analyticAt_of_rightInverse`, the
analytic inverse function theorem, is `analyticAt_of_continuous_branch`
applied with no further analysis.  On top of it,
`Fabius.exists_analyticAt_of_rightInverse`: a continuous right inverse of a
densely analytic function is analytic somewhere.

`Fabius.IsElementaryOrInverse` closes the elementary functions under
continuous inverse branches at any depth, and
`IsElementaryOrInverse.dense_analyticLocus` shows the enlarged class is still
densely analytic.  Its constructor localizes the inverse identity and
continuity to an open `U`, while requiring the chosen totalization to be
analytic at every `y ∈ interior Uᶜ`.  This clause constrains the selected
extension of the branch rather than following automatically from `Mathlib`'s
junk values; a constant extension satisfies it, and `U = ∅` reduces it to
"`g` is entire".  A branch-domain boundary is excluded from both regions, so
the singular point `-1/e` is compatible with the shape of the criterion.
`Fabius.isElementaryOrInverse_of_lambertW` is nevertheless only a conditional
constructor for a supplied Lambert-`W`-shaped total branch satisfying the
stated hypotheses.  Because `Mathlib` does not define `W`, the development
neither constructs nor verifies a standard real branch.

`InverseNotElementary.lean` applies this to `fabiusInv`:
`fabiusInv_not_analyticAt` and `fabiusInv_analyticAt_iff` pin the analytic
locus of the inverse to `ℝ \ [0,1]`, exactly as for `F`.  In the interior the
argument is the inverse function theorem run backwards, and the one thing to
check is that `F⁻¹` has no critical point.  That is `deriv_fabiusInv_ne_zero`,
now derived from the stronger core results `fabiusInv_hasDerivAt`,
`deriv_fabiusInv`, and `deriv_fabiusInv_pos`: `deriv_fabiusReal_pos` gives
`F' > 0` on `(0,1)`, so `HasDerivAt.of_local_left_inverse` supplies
`(F⁻¹)' = 1 / F'` there.  The core module also bootstraps this reciprocal
formula to `fabiusInv_contDiffOn_Ioo`, proving full smoothness on the open
interval.  It is the only place in the whole workstream where a differential
property of `F`, rather than its failure to be analytic, is used.

An earlier version derived this by differentiating `F⁻¹ ∘ F = id`, which needs
`F⁻¹` to be differentiable and so carried an `AnalyticAt ℝ (fabiusInv F hF) y`
hypothesis — refuted, for every `y ∈ Icc 0 1`, by `fabiusInv_not_analyticAt`
twelve lines below.  The statement was therefore vacuous.  An adversarial
review caught it; the fix strengthens the theorem rather than the wording.

## Historical inverse validation evidence

At immutable source commit `63207d9c7`, the originating workstream reported a
clean `lake build +FabiusFunction.InverseNotElementary`; twelve checked
statements had axiom set `[propext, Classical.choice, Quot.sound]`.  Commit
`22f802725` separately recorded three successful `pdflatex` passes for the
inverse-enhanced paper, while explicitly noting that the subsequently changed
Lean closure still required rebuilding.

At immutable source commit `703dd4ed4`, the originating workstream reported a
clean rebuild of the 35-module `InverseNotElementary` closure and a generated
`#print axioms` sweep over all 95 theorems exported by `ElementaryFunction`,
`AlgebraicBranch`, `NotElementary`, `InverseBranch`, and
`InverseNotElementary`.  The report recorded axiom set
`[propext, Classical.choice, Quot.sound]` for every theorem and no `sorryAx`.

At immutable follow-up commit `9d76a07b3`, the originating workstream reported
focused builds of `FabiusFunction.InverseBranch` and
`FabiusFunction.InverseNotElementary`, followed by a post-documentation
combined build, after adding the relative analytic-density strengthening.  It
did not report a new 95-theorem axiom sweep.

At immutable source commit `b164f3d2f`, the originating workstream reported
direct Lean checks and focused builds for `FabiusFunction.FabiusInverse` and
`FabiusFunction.InverseNotElementary`, an aggregate `+FabiusFunction` build,
and a facade axiom audit with only the standard axioms.  This is reported
evidence for the core first-order inverse calculus at that exact commit.

At immutable follow-up commit `c62a56d95`, the originating workstream reported
focused builds after adding full interior smoothness as
`Fabius.fabiusInv_contDiffOn_Ioo`, a successful 4007-job aggregate
`+FabiusFunction` build, and a facade axiom audit with only the standard axioms.
This is reported evidence for full interior smoothness at that exact commit.

These are immutable historical component reports.  They do not validate the
exact manually resolved post-merge tree, and they do not compile or otherwise
cover the current-only `FabiusQBinomialTaylor` coefficient/degree batch.  Exact
combined-tree focused and aggregate builds and an axiom audit remain pending.

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
