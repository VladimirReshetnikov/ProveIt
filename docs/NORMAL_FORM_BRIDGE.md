# Next steps for the infinite normal-form bridge

This implementation note records the assessment made on 2026-09-22. The
repository proves evaluation, arithmetic, valuation, leading coefficients,
and real order for **finite** normal forms. It now constructs a canonical cut
candidate for every small formal normal form, with recursive residual bounds,
leading data and negation. Comparison and bounded extraction now make it an
order isomorphism with the actual surreal carrier. Arithmetic preservation
and compatibility with strong sums remain open.
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

## Constructed recursive candidate

[`SmallNormalFormTruncation.lean`](../Surreal/Foundations/SmallNormalFormTruncation.lean)
proves support and coefficient formulas for exponent and ordinal truncations,
including the successor-term identity. Recursion on the strictly decreasing
support length in
[`SmallNormalFormEvaluation.lean`](../Surreal/Foundations/SmallNormalFormEvaluation.lean)
then defines `cutEvaluation F`. At each supported growth exponent `a`, it obeys

```text
↑(-a) < valuation (cutEvaluation F -
  (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a)).
```

Length induction proves compatibility of every recursive center, so the
definition's fallback branch is never used. The result is a prefix of every
solution of these constraints; uniqueness is asserted only with that
simplicity condition. The empty form gives zero.

[`SignSequenceLeadingTerm.lean`](../Surreal/Foundations/SignSequenceLeadingTerm.lean)
transfers leading-term removal and identifies leading data from a strict
residual bound. Consequently
[`SmallNormalFormLeading.lean`](../Surreal/Foundations/SmallNormalFormLeading.lean)
identifies the first formal exponent and coefficient with the actual leading
data. It preserves and reflects zero, positivity and nonnegativity.
[`SmallNormalFormNegation.lean`](../Surreal/Foundations/SmallNormalFormNegation.lean)
proves negation preservation by length induction and two prefix comparisons.
The following modules supply comparison and extraction independently of arithmetic.

## Comparison, birthday bounds, and inverse extraction

[`SmallNormalFormCutTruncation.lean`](../Surreal/Foundations/SmallNormalFormCutTruncation.lean)
proves that every truncation evaluates to a prefix and extends the residual
bound to every exponent, including gaps in the support. If a cutoff is
absent from the support, reverse well-foundedness supplies the greatest
remaining exponent; if there is none, truncation retains the entire form.
[`SmallNormalFormComparison.lean`](../Surreal/Foundations/SmallNormalFormComparison.lean)
then compares two candidates at the greatest exponent where their forms
differ. Their earlier truncations agree, so subtraction of the two residual
bounds determines the actual difference's leading coefficient. This proves
injectivity, full order comparison, and a valuation comparison for differences
without assuming additivity.

[`SmallNormalFormConstants.lean`](../Surreal/Foundations/SmallNormalFormConstants.lean)
proves exact evaluation of real constants. Every singleton candidate is a
prefix of its corresponding actual monomial. A proper prefix of a real has finite birthday and
is dyadic, which gives the rigidity needed at exponent zero.
[`SmallNormalFormMonomials.lean`](../Surreal/Foundations/SmallNormalFormMonomials.lean)
also proves exact evaluation of `single a 1` as `omegaPower a`: the native
omega cut is a prefix of every positive representative of its valuation
class, providing the reverse simplicity relation. General real coefficients
at arbitrary exponents remain to be handled.

[`SmallNormalFormBirthday.lean`](../Surreal/Foundations/SmallNormalFormBirthday.lean)
bounds support length by the candidate's birthday. A partial form is required
to satisfy **all center bounds for the target**, a stronger invariant than
being a sign prefix of it. In
[`SmallNormalFormExtension.lean`](../Surreal/Foundations/SmallNormalFormExtension.lean),
a nonzero residual has a leading exponent below the entire retained support;
appending its leading term preserves those bounds and strictly extends the
candidate's sign prefix.

[`SmallNormalFormPartialChain.lean`](../Surreal/Foundations/SmallNormalFormPartialChain.lean)
embeds all partial approximations to a fixed target into the ordinal interval
bounded by its birthday. They are therefore small before any maximality
argument is applied. Formal initial segments and their small chain unions are
constructed in
[`SmallNormalFormInitialSegment.lean`](../Surreal/Foundations/SmallNormalFormInitialSegment.lean),
[`SmallNormalFormInitialEvaluation.lean`](../Surreal/Foundations/SmallNormalFormInitialEvaluation.lean),
and [`SmallNormalFormUnion.lean`](../Surreal/Foundations/SmallNormalFormUnion.lean).
Every union exponent already occurs in a stage with the same earlier
truncation and coefficient, so the target's center constraints persist.

Finally,
[`SmallNormalFormExtraction.lean`](../Surreal/Foundations/SmallNormalFormExtraction.lean)
uses Mathlib's Zorn lemma on this small collection. A maximal partial form
cannot have nonzero residual, because the proved extension would contradict
maximality. Thus `cutEvaluation_surjective` and `cutEvaluation_injective`
give `cutEvaluationOrderIso`, with inverse `normalForm`. Both inverse laws
and the zero, negation, ordinary-real, and Conway-monomial formulas are proved. This is an
order isomorphism; no field isomorphism or strong-sum law is inferred from it.

## Remaining dependency order

1. Prove exact evaluation of singleton monomials with arbitrary real
   coefficients and agreement with the existing finite ring evaluation.
   Real constants and unit-coefficient Conway monomials are already proved.
2. Prove the substantive simplicity and truncation compatibility results
   needed for canonical choices to preserve addition and multiplication.
   Merely showing both sides satisfy approximation bounds is insufficient.
3. Package the resulting ordered field isomorphism, then transport the
   fixed-Hahn closedness and localization theorems to actual surreal data.
4. Prove preservation of strong sums, standard part, and admissible Taylor
   evaluation, with coherence under exponent enlargement and universe lifts.
   Extend the real bridge to surcomplex numbers through the coordinate field
   construction.

The order isomorphism and inverse extraction remove the previous existence
and termination obligations. They do not remove the arithmetic obligations.
The existing Hahn closure and Hensel theorems can be transferred only after
the requisite field bridge is proved; they were not assumptions in the
construction of the canonical order isomorphism.
