# Next steps for the infinite normal-form bridge

This implementation note records the assessment made on 2026-09-22. The
repository proves evaluation, arithmetic, valuation, leading coefficients,
and real order for **finite** normal forms. It does not yet construct infinite
normal-form evaluation or an equivalence with the actual surreal carrier.
The obligations are those in `found:eq:normalform`, `found:sub:bridge`, and
`found:thm:workspace` of the [foundations report](foundations-and-computation/foundations/article.tex).

## Verified upstream reuse

The existing vendored revision is
`3c6dcdbc1ce9e4a16f9b6aa16ee485a744568404` of `vihdzp/combinatorial-games`.
Its [Surreal/HahnSeries/Basic.lean](https://raw.githubusercontent.com/vihdzp/combinatorial-games/3c6dcdbc1ce9e4a16f9b6aa16ee485a744568404/CombinatorialGames/Surreal/HahnSeries/Basic.lean)
is now vendored byte for byte and used by
[`SmallNormalForm.lean`](../Surreal/Foundations/SmallNormalForm.lean).

It provides `SurrealHahnSeries.{u} : Type (u + 1)`, an ordered field of real
Hahn series with reverse well-ordered, `u`-small surreal support. Reusable
constants include `mk`, `small_support`, `length`, `exp`, `coeffIdx`, `trunc`,
`truncIdx`, `length_truncIdx`, `length_trunc_lt`, and `term`. It contains no
evaluation map or normal-form equivalence with actual surreal numbers.

The unmodified pinned file compiles with this repository's Lean/Mathlib 4.32
toolchain. The initial independent transitive audit of its 106
`SurrealHahnSeries` declarations accepted only `propext`, `Classical.choice`,
and `Quot.sound`. Its sole combinatorial-games import, `Surreal.Pow`, is
already vendored; its other imports are Mathlib modules. The file has an
Apache-2.0 header and the existing upstream license applies. Reuse adds one
upstream module without a compatibility patch or a shared Mathlib change.
The root audit now also checks the `SurrealHahnSeries` namespace. The local
interface exposes small reverse-well-ordered support and ordinal truncations
with actual sign-sequence growth exponents; it supplies no infinite evaluation.

Upstream HEAD resolved to `02b4a908ea2ecfefffecb438f691951a814a5264` during
inspection. Its Hahn directory still contained only `Basic.lean`; changes
from the pinned file concern compatibility and names, and its `Leading.lean`
was byte-identical. Updating the dependency would not supply the missing
bridge. This is a finding about those two inspected revisions.

## Available local ingredients

- `SignSequence.cut`, `cut_realizes`, and `cut_isPrefix` construct the simplest
  separator of a small cut. `existsUnique_prefix_of_ordConnected` also packages
  simplest-element uniqueness for nonempty convex sets.
- `SignSequence.valuation`, `tMonomial`, `valuation_div`, and
  `isInfinitesimal_iff_forall_nat_abs_lt` express scaled approximation through
  ordinary inequalities. The finite normal-form modules supply exact leading
  data and arithmetic.
- Vendored `Surreal.mk_lt_mk_sub_leadingTerm` proves that removing a nonzero
  leading term strictly increases valuation. It does not prove termination
  of transfinite leading-term extraction.
- Native `HahnSeries.truncLT` and `SummableFamily` already handle formal
  truncations and strong sums. `hahnEmbedding_isOrderedAddMonoid` only supplies
  an additive-group embedding; it does not supply the required multiplicative,
  monomial-preserving normal-form bridge.

## Constructed compatible-ball intersection

For `I : Type u` and `p a : I → SignSequence.{u}`, assume

```text
∀ i j, ↑(min (a i) (a j)) < valuation (p i - p j).
```

The checked theorem `existsUnique_simplest_valuationBall_point` now gives a unique *simplest* `x` satisfying
`∀ i, ↑(a i) < valuation (x - p i)`: it satisfies these inequalities and is
a sign prefix of every other solution. It is implemented in
[`SignSequenceValuationBalls.lean`](../Surreal/Foundations/SignSequenceValuationBalls.lean).

The proof uses the scaled absolute-bound characterization for all reciprocal
positive natural numbers and forms the small cut with options
`p i ± tMonomial (a i) / (n + 1)`, indexed by `I × ℕ`. Compatibility separates
the options; `cut_realizes` gives the approximation bounds and `cut_isPrefix`
gives simplicity. The empty index type is included. No Hensel or
real-closedness assumption enters this construction.

**Approximation is not uniqueness.** Small strict upper bounds give an exponent
`b` above every `a i`. If `x` satisfies the bounds, so does
`x + tMonomial b`. Thus approximation inequalities alone cannot identify a
sum, prove an arithmetic identity, or select a normal form. This nonuniqueness is proved in
[`SignSequenceValuationApproximation.lean`](../Surreal/Foundations/SignSequenceValuationApproximation.lean).
The simplicity condition is essential.

## Dependency order after that lemma

1. The pinned small-support module and its ordinal truncation APIs are now reused.
   Retain `Small.{u}` support explicitly; finite evaluation's independent
   universe parameters do not justify arbitrary infinite supports.
2. Construct evaluation by ordinal-length recursion, with the prescribed
   successor terms and simplest choices at limit stages. Prove the intended
   residual valuation and coefficient statements at each truncation.
3. Prove the substantive simplicity and truncation compatibility results
   needed for canonical choices to preserve addition and multiplication.
   Merely showing both sides satisfy approximation bounds is insufficient.
4. Extract the normal form of every actual surreal. Prove a birthday bound
   and termination at a small ordinal, then the inverse laws. Strictly
   increasing valuations alone do not prove termination.
5. Prove preservation of strong sums, standard part, and admissible Taylor
   evaluation, with coherence under exponent enlargement and universe lifts.
   Extend the real bridge to surcomplex numbers through the coordinate field
   construction.

These remain separate proof obligations. The existing Hahn closure and Hensel
theorems can be transferred only after the requisite bridge is proved; they
are not assumptions for constructing it.
