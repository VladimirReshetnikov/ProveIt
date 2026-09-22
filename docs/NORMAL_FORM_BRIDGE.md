# Next steps for the infinite normal-form bridge

This implementation note records the assessment made on 2026-09-22. The
repository proves evaluation, arithmetic, valuation, leading coefficients,
and real order for **finite** normal forms. It now constructs a canonical cut
candidate for every small formal normal form, with recursive residual bounds,
leading data and negation. Comparison and bounded extraction now make it an
ordered field isomorphism with the actual surreal carrier. Small-family
localization now transfers odd-degree roots from divisible Hahn workspaces,
proving real closedness. Actual surcomplex algebraic closedness, valuation
and standard-part preservation, exponent-workspace coherence, and small
strong real sums are now constructed as well.
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
class, providing the reverse simplicity relation. The general real-coefficient case is now proved below.

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
order isomorphism; arithmetic requires the separate proofs below.

## Arithmetic compatibility

[`SmallNormalFormRealMonomials.lean`](../Surreal/Foundations/SmallNormalFormRealMonomials.lean)
proves evaluation of `single a r` as `ofReal r * omegaPower a` for every real
coefficient, including zero and both signs. A product presentation of the
real coefficient and omega power has option gaps whose valuations are at
most the monomial's threshold. A higher-valuation error preserves all of
these bounds, giving the reverse prefix needed for equality.

[`SignSequenceSumCutSimplicity.lean`](../Surreal/Foundations/SignSequenceSumCutSimplicity.lean)
and [`SmallNormalFormSumSimplicity.lean`](../Surreal/Foundations/SmallNormalFormSumSimplicity.lean)
express realization of the Conway sum cut by two translated approximation
invariants. Nested induction on the support lengths in
[`SmallNormalFormAddition.lean`](../Surreal/Foundations/SmallNormalFormAddition.lean)
shows both that the actual sum approximates the formal sum and that the
formal sum's value realizes this Conway cut. Mutual prefix simplicity gives
`cutEvaluation_add`, without needing extraction or approximation uniqueness.

For multiplication,
[`SmallNormalFormProductFrontier.lean`](../Surreal/Foundations/SmallNormalFormProductFrontier.lean)
selects supported factor exponents `a,b` for every supported product exponent
`a+b`. Products involving the earlier truncations determine the product
strictly above `a+b`, and the remaining product of tails has leading
coefficient `coeff F a * coeff G b` there. In
[`SmallNormalFormMultiplication.lean`](../Surreal/Foundations/SmallNormalFormMultiplication.lean),
induction on the two actual birthdays identifies those earlier products.
Leading-term arithmetic controls the remaining tail product and proves all
center constraints. Canonical Conway product options, pulled back by
extraction, supply the opposite prefix comparison. Thus `cutEvaluation_mul`
holds for arbitrary small supports.

[`SmallNormalFormAddEquiv.lean`](../Surreal/Foundations/SmallNormalFormAddEquiv.lean)
and [`SmallNormalFormFieldEquiv.lean`](../Surreal/Foundations/SmallNormalFormFieldEquiv.lean)
package the resulting ordered additive and field isomorphisms. Inversion,
division, powers and rational casts are consequences of the native field
homomorphism API, with the fields' totalized zero conventions.
[`SmallNormalFormFiniteEvaluation.lean`](../Surreal/Foundations/SmallNormalFormFiniteEvaluation.lean)
proves agreement with the independent finite monoid-algebra evaluation.

[`SmallNormalFormHahnEmbedding.lean`](../Surreal/Foundations/SmallNormalFormHahnEmbedding.lean)
embeds an entire small real Hahn workspace into the formal field. Negating
the exponent map converts increasing valuation exponents to decreasing
growth exponents. Coefficients and support are preserved exactly, and the
map is an injective ring homomorphism.
[`SignSequenceHahnEmbedding.lean`](../Surreal/Foundations/SignSequenceHahnEmbedding.lean)
composes it with the field equivalence to embed the whole workspace into
actual surreals, preserving the native lexicographic order and sending
each singleton to its real coefficient times the corresponding t-monomial.

## Small workspaces and real closedness

[`SmallNormalFormWorkspace.lean`](../Surreal/Foundations/SmallNormalFormWorkspace.lean)
pulls coefficients back along the negative exponent map. The pullback recovers
a form whenever its support lies in that image. The rational span of the
union of a small family's supports therefore supplies one small divisible
workspace and exact preimages for the entire family. Mathlib's polynomial
lifts API then descends every polynomial to this common workspace.

[`SmallNormalFormRealClosed.lean`](../Surreal/Foundations/SmallNormalFormRealClosed.lean)
uses injectivity to preserve polynomial degree and transfers the proved Hahn
odd-degree root theorem. The actual sign field's independently constructed
nonnegative square roots transport in the other direction. This proves
`IsRealClosed SmallNormalForm` without assuming closedness of either field.
[`SignSequenceRealClosed.lean`](../Surreal/Foundations/SignSequenceRealClosed.lean)
transfers odd-degree roots through the field equivalence and combines them
with the existing genetic square roots to prove `IsRealClosed SignSequence`.

[`SignSequenceWorkspace.lean`](../Surreal/Foundations/SignSequenceWorkspace.lean)
packages exact simultaneous preimages for any small actual family. The image
is a small subfield, and polynomial descent preserves degree.
[`Surcomplex/AlgebraicallyClosed.lean`](../Surreal/Surcomplex/AlgebraicallyClosed.lean)
extends the actual real Hahn embedding coordinatewise through the native
quadratic/Hahn equivalence. Both coordinates of all polynomial coefficients
lie in one small divisible workspace. Its complex Hahn field supplies roots
of positive-degree polynomials, proving `IsAlgClosed Surcomplex` and the
linear factorization and root-multiplicity formulas.

[`SignSequenceHahnValuation.lean`](../Surreal/Foundations/SignSequenceHahnValuation.lean)
identifies actual valuation with the embedded least Hahn exponent, retaining
infinity at zero, and preserves the leading real coefficient. Finiteness
and infinitesimality agree with nonnegative and positive Hahn order. On the
finite domain, subtracting the zero coefficient leaves positive order, so
the actual standard part is exactly that coefficient.
[`Surcomplex/HahnValuation.lean`](../Surreal/Surcomplex/HahnValuation.lean)
uses the minimum of the two coordinate orders to prove the corresponding
complex valuation, finiteness, infinitesimality and standard-part formulas.

## Strong sums and exponent-workspace coherence

[`SignSequenceStrongSummation.lean`](../Surreal/Foundations/SignSequenceStrongSummation.lean)
defines strong summability on canonical normal forms by the native Hahn
conditions: a partially well-ordered support union and finite coefficient
fibers. A small index type gives a small support union and hence a small
coefficientwise sum. Evaluation defines its actual strong sum; extracting
the normal form recovers exactly the formal sum, coefficient by coefficient.
Native Hahn workspace summable families remain strongly summable after
actual evaluation, and evaluation commutes with their small strong sums.

[`SignSequenceHahnCoherence.lean`](../Surreal/Foundations/SignSequenceHahnCoherence.lean)
and [`Surcomplex/HahnCoherence.lean`](../Surreal/Surcomplex/HahnCoherence.lean)
prove that embedding exponents into a larger small workspace and then
evaluating agrees with evaluation along the composite exponent map.
The identities hold for complete ring maps and arbitrary Hahn supports.

## Remaining dependency order

1. Extend strong summation to complex families and construct admissible
   univariate and multivariate Taylor evaluation on actual numbers.
2. Prove compatibility under universe lifts and the remaining complex
   leading-data and analytic-operation correspondences.

Existence, inverse extraction, real monomials, finite evaluation and field
arithmetic are now proved. Small real strong sums and exponent-workspace
coherence are also proved. The remaining clauses above require their own
constructions before the entire workspace theorem is covered.
