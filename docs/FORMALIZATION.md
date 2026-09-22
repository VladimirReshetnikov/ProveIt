# Formalization coverage and dependency ledger

The objective is to formalize **all mathematical results in the repository's
surreal and surcomplex documents**, including their hypotheses and size
restrictions. This ledger starts from the main reports; it is not a reduction
of that objective to the statements easiest to count or prove.

The implementation plan is the foundations report,
[`foundations/article.tex`](foundations-and-computation/foundations/article.tex),
especially `found:sec:architecture`, `found:sub:layers`,
`found:sub:contracts`, and `found:sub:milestones`. The report describes a
proposal, not an existing implementation. The preserved Lean sketches under
its `code/` directory are source artifacts; their presence does not establish
that the current Lean target compiles or imports them.

## Scope and how to read this ledger

The canonical inventory below identifies **22 main reports** and records all
**950** literal `theorem`, `lemma`, `proposition`, and `corollary` environments
in those reports. Relative to `796f8d4`, the refreshed corpus adds 213 such
statements in four new reports and 19 in `surcomplex/contours-and-stokes`,
for 232 additional main-report statements. These new proof obligations remain
**pending unless mapped below**, with source corrections noted separately.

Counts are a navigation aid, **not a completeness certificate**: examples,
equations, prose assertions, short proofs, and archived manuscripts also
contain mathematical claims. The foundations README's count of 30
theorem-environment results includes six examples and a design principle;
the narrower inventory here counts its 23 theorem/lemma/proposition/corollary
statements.

There are also **54 preserved source manuscripts** under `sources/`. Their
1339 literal standard result environments are not 1339 additional independent
results: merged reports deliberately overlap them, and some change scope or
resolve conflicting definitions. A complete coverage audit must map each source
claim to an equivalent main-report statement, a separate proof obligation, or
a documented mathematical correction. No such equivalence is presumed here.
The unnumbered companion texts
[`short-proof.tex`](surreal/hahn-evaluation-at-omega/short-proof.tex) and
[`short_proof.tex`](surreal/genetic-gaps-and-primitives/short_proof.tex)
likewise need claim-by-claim reconciliation. Existing program checks and LaTeX
build records do not prove the mathematical statements in Lean.

Statuses are deliberately strict:

- **Pending**: no checked Lean theorem has yet been mapped to the entire source
  statement, with all its hypotheses and conclusions.
- **Prerequisites proved**: some reusable algebra or an abstract conditional
  theorem is checked; the full source statement remains pending.
- **Proved**: an imported, compiled Lean declaration matches the full statement,
  and its axiom dependencies have been inspected. A conditional theorem counts
  only for its stated hypotheses; instantiation at surreal numbers needs its
  own checked construction or bridge.
- **Needs correction**: a stated claim is false or underspecified as written;
  record the counterexample or missing hypothesis before formalizing a corrected
  statement. Never conceal this state with `axiom`, `sorry`, or an impossible
  typeclass assumption.

The main-report index is **pending unless mapped below**, with the
implementation table recording progress at the precise clause level.
A checked abstract theorem is not a construction of the surreal ordered field
or a normal-form bridge.

Reuse the pinned Mathlib library before rebuilding its constructions: the
initial algebra uses `QuadraticAlgebra`, `IsRealClosed`, `IsAlgClosed`, and
existing polynomial factorization/extension results. Repository declarations
should expose the manuscript correspondence and prove the genuinely missing
bridges rather than duplicate the library.

The independently maintained `combinatorial-games` library supplies the
numeric-game quotient and its proved ordered field. A
[vendored dependency](../vendor/combinatorial-games/README.md) records the
exact upstream revision, 27-module import closure, Apache license and three
proof-script compatibility changes for the pinned Lean/Mathlib version.
No mathematical statement or arithmetic definition is changed. Its field
construction is included in the transitive axiom audit. An explicit order
isomorphism with the existing sign carrier now preserves every small cut
and its already constructed additive structure. Transporting multiplication
and inverse gives a proved ordered field on that same sign carrier.
Real closedness and the Hahn normal-form bridge remain separate obligations.

## Implementation mappings

The mapped modules pass `lake build`, including the default `SurrealAudit`
target. The audit checks every imported `Surreal` declaration and rejects any
transitive axiom beyond `propext`, `Quot.sound`, and `Classical.choice`. All ten
size-obstruction theorems have no axiom dependencies. This establishes the
listed Lean statements, not the outstanding surreal interpretation. Every
main-report statement not fully covered below remains pending, including
remaining clauses of a partially mapped statement.

| Source obligation | Lean declarations | Scope of current implementation |
|---|---|---|
| `found:prop:allcuts` | `Surreal.Foundations.noUniversalStrictBound`, `noUnrestrictedStrictBounds`, `noUnrestrictedUpperBounds`, `noUnrestrictedCuts` in [SizeObstructions.lean](../Surreal/Foundations/SizeObstructions.lean) | Full unrestricted-bound and two-sided-cut contradiction for an arbitrary irreflexive relation. **Proved**; integrated build and axiom audit pass. |
| `found:sub:cutdata` | `Surreal.Foundations.SmallCutData`, `SmallCutData.IsRealizedBy`, `HasSmallCutFillers`, `HasSmallStrictUpperBounds` | Size-aware data and explicit abstract properties. Reindexing, the small-set interface, and the constructed sign-carrier model are mapped below. |
| `found:lem:bounds` | `Surreal.Foundations.HasSmallCutFillers.hasSmallStrictUpperBounds`, `HasSmallCutFillers.exists_strict_lower_bound`, `HasSmallCutFillers.exists_strict_lower_bound_above`, `HasSmallStrictUpperBounds.exists_bound_of_small_set` | Upper/lower/positive-lower bounds conditional on a proved small-cut-filler property. The property and the ordered-field structure are now proved for the sign carrier below. |
| `found:prop:universecut` | `Surreal.Foundations.not_small_of_small_strict_upper_bounds`, `not_small_of_small_cut_fillers` | The abstract non-smallness implication using Mathlib `Small`. The explicit relative-universe application is proved below on the same sign carrier whose ordered-field structure is now constructed. |
| `found:sub:properness`, `found:prop:proper`, birthday-bounded fragment assertion | `Surreal.Foundations.SignSequence`, `ofSigns`, `birthdays_bounded`, `small_bounded`, `not_small` in [SignSequence.lean](../Surreal/Foundations/SignSequence.lean) | A concrete carrier in `Type (u+1)` has an ordinal birthday in `Ordinal.{u}` and a zero-extended two-sign sequence. Arbitrary ordinal-length Boolean sign data construct elements. Every `u`-small family has strictly bounded birthdays, and every fixed birthday fragment (even with a non-strict bound) is `u`-small. The whole carrier is not `u`-small because its birthday map is onto all `u`-ordinals. This is the precise relative-universe properness assertion, not a set-theoretic proper class inside Lean. **Proved** for the constructed sign carrier; build and axiom audit pass. |
| Linear order, ordinal embedding, prefix simplicity and option-size clauses of `found:sub:signs`; `found:rem:simplicity` | `Surreal.Foundations.SignSequence.lt_iff`, `ordinalOrderEmbedding`, `IsPrefix`, `simpler_wellFounded`, `truncate`, `small_leftIndex`, `small_rightIndex`, `canonicalCut`, `canonicalCut_realized`, `neg_lt_neg_iff`, `birthday_precedence_not_prefix` in [SignSequence.lean](../Surreal/Foundations/SignSequence.lean) | Numerical order is Mathlib's lexicographic first disagreement with `-1 < termination < 1`. Prefix simplicity is separately well-founded by birthday; an explicit one-plus/two-minus example refutes the converse from birthday precedence. All-plus signs embed ordinals as an order embedding, with no claim about ordinary ordinal arithmetic. Sign reversal reverses numerical order. Canonical left/right options are the truncations before plus/minus signs, with lower-universe indices and a proved separator. Field arithmetic and arbitrary small-cut filling are not assumed. **Proved** for the sign carrier; build and axiom audit pass. |
| Simplest-separator clause of `found:sub:signs` | `Surreal.Foundations.SignSequence.isPrefix_of_separates_options`, `canonicalCut_isPrefix`, `canonicalCut_simplest` in [SignSequenceOptions.lean](../Surreal/Foundations/SignSequenceOptions.lean) | Every separator of the actual canonical small option families extends the original sequence. Thus the sequence is the unique separator of minimum birthday, including the empty sequence. The proof proceeds by well-founded induction over sign positions and uses the numerical truncation comparisons. This concerns canonical cuts; filling arbitrary small separated families and the resulting cut operation are mapped below. **Proved** for the sign carrier; build and axiom audit pass. |
| Upper-bound clause of `found:lem:bounds` on the constructed sign carrier | `Surreal.Foundations.SignSequence.lt_ofOrdinal_of_birthday_lt`, `small_strict_upper_bounds` in [SignSequence.lean](../Surreal/Foundations/SignSequence.lean) | An all-plus sequence of greater birthday bounds a given sequence numerically. Birthday bounds therefore prove the existing `HasSmallStrictUpperBounds` property for the actual carrier, without postulating general cut fillers. The other cut-based bounds and the ordered-field structure on the same carrier are mapped below. **Proved**; build and axiom audit pass. |
| `found:sub:cutdata`, indexed/predicate interface and reindexing assertion | `Surreal.Foundations.SmallCutData.reindex`, `reindex_isRealizedBy_iff`, `ofSmallSets`, `ofSmallSets_isRealizedBy_iff`, `HasSmallCutFillers.exists_separator_of_small_sets` in [SmallCutData.lean](../Surreal/Foundations/SmallCutData.lean) | Reindexing by equivalences preserves exactly the separator predicate. Two predicate-based option sets give lower-universe indexed cut data when both element types carry explicit `Small` witnesses. The separator equivalence is proved in both directions. This interface introduces no filler axiom. **Proved**; build and axiom audit pass. |
| Recursive comparison formula `found:eq:comparison` on canonical signs | `Surreal.Foundations.SignSequence.le_iff_options_lt`, `lt_iff_exists_option`, `le_iff_canonicalCut` in [SignSequenceComparison.lean](../Surreal/Foundations/SignSequenceComparison.lean) | Numerical comparison is equivalent to the Conway rule using canonical left options of the first number and right options of the second. Strict comparison has an option witness. The lower-universe canonical-cut version is included. This is a theorem for the extensional sign carrier, not a construction or quotient of raw games. **Proved**; build and axiom audit pass. |
| Simplest-number uniqueness in `found:sub:choice` and `found:sub:package` | `Surreal.Foundations.SignSequence.isPrefix_of_minimum_birthday`, `existsUnique_prefix_of_ordConnected`, `existsUnique_minimum_birthday_of_ordConnected`, `existsUnique_simplest_separator` in [SignSequenceSimplicity.lean](../Surreal/Foundations/SignSequenceSimplicity.lean) | Every nonempty order-convex set has a unique minimum-birthday element, which is a prefix of all its members. Separators form such a convex set. The simplicity theorem requires separator existence; that independent construction follows below. Unrestricted predicates occur here only with nonempty convexity, not as unrestricted cut inputs. **Proved**; build and axiom audit pass. |
| Small-cut construction and rank bound in `found:sub:signs`, `found:sub:cutdata`, `found:sub:package` | `Surreal.Foundations.SignSequence.exists_cut_separator_of_birthday_lt`, `small_cut_fillers` in [SignSequenceCut.lean](../Surreal/Foundations/SignSequenceCut.lean); `cut`, `cut_realizes`, `cut_isPrefix`, `cut_eq_iff`, `birthday_cut_le_iSup`, `cut_canonicalCut`, `cut_congr`, `cut_reindex` in [SignSequenceCutOperation.lean](../Surreal/Foundations/SignSequenceCutOperation.lean) | A fixed-length Boolean lexicographic complete lattice constructs a separator at any ordinal birthday strictly bounding all option birthdays, including limit bounds and empty cuts. Ordinal well-foundedness then selects the unique simplest separator. Its birthday is bounded by the small supremum of successor option birthdays, and it is a prefix of every separator. Canonical options reconstruct the original number; equal separator predicates and reindexing preserve the value. All cut indices remain in `Type u` while the carrier is in `Type (u+1)`. No unrestricted cut axiom or field structure is used. **Proved** for the concrete sign carrier; build and axiom audit pass. |
| `found:eq:negcut`; remaining bound clauses of `found:lem:bounds` | `Surreal.Foundations.SignSequence.negateCut`, `cut_negateCut`, `exists_strict_lower_bound`, `exists_positive_lower_bound`, `exists_separator_of_small_sets` in [SignSequenceCutOperation.lean](../Surreal/Foundations/SignSequenceCutOperation.lean) | Swapping and negating the option families makes the actual simplest cut value equal to the sign reversal of the original value. Small families have lower bounds and positive families have positive strict lower bounds, including empty families. Small predicate-based cuts are also filled. Numerical density and absence of endpoints are proved instances. The arithmetic construction, its recursive addition law and the ordered-field structure are mapped below. **Proved** for the sign carrier; build and axiom audit pass. |
| Cut-based generalization following `found:prop:incomplete`, and its order-theoretic counterexample | `Surreal.Foundations.SignSequence.exists_smaller_upper_bound`, `no_isLUB_of_no_greatest`, `finite_ordinals_bounded_without_supremum` in [SignSequenceBounds.lean](../Surreal/Foundations/SignSequenceBounds.lean) | Every proposed upper bound of a small set without a greatest member has a strictly smaller upper bound. Embedded finite ordinals form a nonempty bounded small set with no supremum. Thus the constructed numerical order is not Dedekind complete. Native natural/integer casts and the subtraction-by-one proof are constructed below. The alternative halving proof is provided below using the constructed field. **Proved** for the order assertion; build and axiom audit pass. |
| `found:eq:comparison` for arbitrary small presentations and its option-domination consequences | `Surreal.Foundations.SignSequence.cut_le_cut_iff`, `cut_le_iff`, `le_cut_iff`, `cut_lt_cut_iff`, `cut_le_cut_of_options`, `leftOption_cut_le`, `le_rightOption_cut` in [SignSequenceCutComparison.lean](../Surreal/Foundations/SignSequenceCutComparison.lean) | The comparison rule holds for arbitrary small separated cut presentations. Every canonical left option is dominated by an original left option, and every canonical right option is above an original right option. Only these directions are asserted; redundant presentation options need not be canonical. The proof uses separator simplicity, not a supremum interpretation of cuts. **Proved**; build and axiom audit pass. |
| `found:sub:recursionmeasure`; nested canonical option prerequisite for `found:eq:addcut` | `Surreal.Foundations.SignSequence.PairSimpler`, `pairSimpler_wellFounded`, the four canonical option decrease lemmas, `numerical_not_wellFounded`, `maximum_birthday_not_decreasing`, `ordinal_sum_birthday_not_decreasing` in [SignSequenceRecursion.lean](../Surreal/Foundations/SignSequenceRecursion.lean); `truncate_truncate`, `IsPrefix.truncate_eq`, `left_right_option_nested` in [SignSequenceTruncation.lean](../Surreal/Foundations/SignSequenceTruncation.lean) | Mathlib's game-addition relation supplies a checked well-founded relation for decreasing one input at a time. Canonical opposite options are nested truncations. Explicit sign sequences show that numerical order is not well founded and that maximum birthday and ordinary ordinal addition fail to decrease in the proposed cases. This proves the relation-based recursion route. A separate natural-sum measure proof is mapped below; the raw multiplication termination argument remains in the reused game library. **Proved**; build and axiom audit pass. |
| `found:eq:addcut`, additive ordered-group obligations following it, and additive portion of `found:sub:package` | `Surreal.Foundations.SignSequence.add`, `add_options_separated`, `addCut`, `add_eq_cut`, `addCut_realizes_iff`, `add_comm`, `add_zero`, `zero_add`, `add_right_strictMono`, `add_left_strictMono`, cancellation laws in [SignSequenceAddition.lean](../Surreal/Foundations/SignSequenceAddition.lean); `sumCut`, `cut_sumCut`, `add_assoc` in [SignSequenceAddAssociative.lean](../Surreal/Foundations/SignSequenceAddAssociative.lean); `add_neg_cancel`, `neg_add_cancel` in [SignSequenceAddInverse.lean](../Surreal/Foundations/SignSequenceAddInverse.lean); native group/order instances in [SignSequenceAddGroup.lean](../Surreal/Foundations/SignSequenceAddGroup.lean) | Actual Conway addition is defined by native well-founded pair recursion. The internal fallback is proved unreachable: all recursive option families are small and separated, using nested canonical options and earlier recursive bounds. The operation obeys the simplest-cut equation, including arbitrary small presentations of both summands. Commutativity, zero, strict translation, cancellation, associativity and inverses are independently proved before assembling `AddCommGroup` and `IsOrderedAddMonoid`; the inverse is the existing sign reversal and the order is the existing numerical order. Multiplication and field inverses are transported through the proved arithmetic equivalence below. Real closedness and the normal-form bridge remain pending. **Proved** for the concrete additive sign carrier; build and axiom audit pass. |
| Integer embedding in `found:sub:package`; native natural-number and subtraction clauses of `found:prop:incomplete` | `Surreal.Foundations.SignSequence.natCast_eq_ofOrdinal`, `intCast_negSucc_eq_neg_ofOrdinal`, `birthday_natCast`, `integerAddHom`, `integerOrderEmbedding`, `range_natCast_eq_finite_ordinals`, `natCast_lt_omega0`, `sub_one_mem_upperBounds_natCast`, `natCast_range_no_isLUB`, `natural_numbers_bounded_without_supremum` in [SignSequenceIntegers.lean](../Surreal/Foundations/SignSequenceIntegers.lean) | The one-plus sequence and actual Conway additive group give native `AddCommGroupWithOne` and `CharZero` instances. Cut induction proves that natural casts are precisely finite all-plus sequences; negative integers are the corresponding sign reversals. Integer casts preserve addition and strictly preserve order. The all-plus sequence of length omega strictly bounds the natural range, and subtracting one from any upper bound gives a smaller upper bound, proving there is no supremum. No multiplication, rational embedding or Archimedean property is assumed. The source's alternative halving argument is proved below in the ordered field. **Proved** for the concrete additive sign carrier; build and axiom audit pass. |
| Closed/discrete-subset and convergent-net clauses of `found:thm:discrete`; no-isolated-points sharpness | `Surreal.Foundations.SignSequence.exists_Ioo_inter_subset_singleton`, `isClosed_of_small`, `isDiscrete_of_small`, `discreteTopology_of_small`, `tendsto_nhds_iff_eventually_eq_of_small_range`, `tendsto_nhds_iff_eventually_eq`, `punctured_nhds_neBot`, `not_discreteTopology` in [SignSequenceTopology.lean](../Surreal/Foundations/SignSequenceTopology.lean) | Native order topology on the concrete carrier has closed/discrete lower-universe-small subsets. Small range suffices for convergence along any filter to be equivalent to eventual equality; small index types are a corollary. The whole carrier is not discrete and has no isolated points. Smallness is retained on the subset/range/index type, never assumed for unrestricted predicates. The self-valued absolute-ball interpretation is proved below. The surcomplex product topology and its squared-radius and actual modulus bases are constructed below. **Proved** for the real sign carrier; build and axiom audit pass. |
| Cauchy-net clause of `found:thm:discrete`, additive uniformity and real-carrier specialization | `Surreal.Foundations.HasSmallCutFillers.exists_pos_lt_abs_sub`, `exists_entourage_eq_on_small_set`, `eventually_constant_of_cauchy_small_range`, `eventually_constant_of_cauchy`, `cauchy_map_iff_eventually_constant` in [SmallCauchy.lean](../Surreal/Foundations/SmallCauchy.lean); concrete uniformity and specializations in [SignSequenceUniformity.lean](../Surreal/Foundations/SignSequenceUniformity.lean) | For ordered additive groups with compatible order topology and native group uniformity, small cut filling gives one positive bound below all nonzero pairwise absolute differences of a small range. An actual entourage therefore forces equality, and native `Cauchy (map f l)` implies eventual constancy along an arbitrary filter; the iff includes `NeBot l`. The constructed sign group's native uniformity preserves its order topology definitionally and has self-valued absolute-difference neighborhood/entourage bases, so the Cauchy conclusion is instantiated on the concrete carrier. No real-valued metric or completeness assumption is used. The corresponding surcomplex uniformity and modulus bridge are proved below. **Proved** for the real additive sign carrier; build and axiom audit pass. |
| `found:ex:largerindex` | `Surreal.Foundations.SignSequence.PositiveNetIndex`, `positiveNet`, `positiveNet_tendsto_zero`, `positiveNet_cauchy`, `positiveNet_not_eventually_zero`, `positiveNet_not_eventually_constant`, `positiveNetIndex_not_small` in [SignSequenceLargeNet.lean](../Surreal/Foundations/SignSequenceLargeNet.lean) | All positive sign sequences, with reverse numerical order, index a nontrivial directed net which converges to zero in the native order topology and is Cauchy in the additive uniformity. Every term is positive and the net is never eventually constant. Its index type is explicitly proved not `Small.{u}`, demonstrating that the small-index hypotheses cannot be removed. Density supplies a smaller positive radius without requiring division by two. The surcomplex inclusion and its larger-index net are constructed below. **Proved** for the concrete real sign carrier; build and axiom audit pass. |
| Comparison and canonical-option part of the sign/game bridge in `found:sub:signs` and `found:sub:twotracks` | `Surreal.Foundations.SignSequence.canonicalGameGraph`, `canonicalGameGraph_move_simpler`, `toIGame`, `leftMoves_toIGame`, `rightMoves_toIGame`, `toIGame_eq`, `toIGame_le_iff`, `toIGame_lt_iff`, `toIGame_equiv_iff`, `numeric_toIGame`, `toSurrealOrderEmbedding` in [SignSequenceGames.lean](../Surreal/Foundations/SignSequenceGames.lean) | Canonical sign options are small move sets decreasing prefix simplicity, so upstream `GameGraph.toIGame` constructs their raw game. Paired well-founded induction proves both comparison orientations before numericity is established. Game equivalence identifies exactly equal sign sequences, and the numeric-game quotient receives an explicit order embedding. This preserves the actual canonical options and numerical order. Arbitrary-cut preservation, surjectivity and arithmetic preservation are proved below before transferring field operations. **Prerequisites proved**; build and axiom audit pass. |
| Zero and unit compatibility in the sign/game bridge | `Surreal.Foundations.SignSequence.toIGame_zero`, `toIGame_one`, `toSurreal_zero`, `toSurreal_one` in [SignSequenceGameConstants.lean](../Surreal/Foundations/SignSequenceGameConstants.lean) | The empty and one-plus sequences give literal equality with the upstream raw games zero and one, hence also preserve these constants in the numeric-game quotient. These are the already constructed sign zero and additive unit. Addition compatibility and transport of multiplication are proved below. **Proved** for these bridge constants; build and axiom audit pass. |
| Numeric-game small-cut route in `found:sub:cutdata`; `found:eq:comparison` | `Surreal.Foundations.gameCut`, `left_lt_gameCut`, `gameCut_lt_right`, `gameCut_realizes`, `game_hasSmallCutFillers`, `gameCut_le_gameCut_iff`, `gameCut_lt_gameCut_iff`, `numericGameCut`, `gameCut_numericGameCut` in [GameCuts.lean](../Surreal/Foundations/GameCuts.lean) | Lower-universe indexed separated option families define cuts in the reused numeric-game quotient. Their values separate the options and obey both recursive comparison formulas. Reindexing a numeric game's small move sets by `Shrink` and mapping them into the quotient reconstructs its original quotient value. This establishes the native game-side interface without assuming a sign equivalence or a canonical quotient representative. **Proved** for the numeric-game carrier; build and axiom audit pass. |
| Order and arbitrary-cut equivalence in `found:sub:signs` and the game/sign route of `found:sub:twotracks` | `Surreal.Foundations.SignSequence.toSurrealCut`, `gameCut_toSurrealCut_canonical`, `toSurreal_cut`, `exists_toSurreal_eq_mk`, `toSurreal_surjective`, `toSurrealOrderIso` in [SignSequenceGameEquiv.lean](../Surreal/Foundations/SignSequenceGameEquiv.lean) | The explicit embedding preserves every small separated cut, including arbitrary presentations and duplicate options. Induction over numeric-game moves constructs a sign preimage for every numeric game using lower-universe indexed option cuts. Quotient induction then gives surjectivity and an actual order isomorphism in the same universe. The proof makes no whole-carrier smallness assumption and does not identify arbitrary separators with cut values. Compatibility with existing addition and transport of field operations are proved below; birthday/simplicity correspondence and the Hahn bridge remain separate. **Proved** for the order and cut equivalence; build and axiom audit pass. |
| Existing-addition compatibility in `found:eq:addcut` and the game/sign bridge | `Surreal.Foundations.SignSequence.toSurreal_add`, `toSurreal_neg`, `toSurreal_sub`, `toSurrealAddHom`, `toSurrealAddEquiv`, `toSurrealOrderAddIso` in [SignSequenceGameAddition.lean](../Surreal/Foundations/SignSequenceGameAddition.lean) | Pair recursion proves that the order/cut equivalence preserves the independently constructed Conway addition by matching all four canonical option families. Negation and subtraction then follow from the existing additive-group laws. The resulting ordered additive equivalence retains the original operations; it does not redefine addition by transport. **Proved**; build and axiom audit pass. |
| Ordered-field structure in `found:sub:package` and arithmetic field laws following `found:eq:mulcut` | `Surreal.Foundations.SignSequence.mul`, `inv`, `signSequenceCommRing`, `signSequenceIsStrictOrderedRing`, `signSequenceField`, `toSurreal_mul`, `toSurreal_inv`, `toSurreal_div`, `toSurrealRingEquiv` in [SignSequenceField.lean](../Surreal/Foundations/SignSequenceField.lean) | The explicit equivalence transports the reused numeric-game multiplication and total inverse onto the sign carrier. Ring and field laws are proved while retaining the existing additive group with one and numerical order; the same map is a field isomorphism. No new mathematical axioms or real-closedness premise are introduced. The native genetic product-cut equation is proved below; real closedness and the Hahn normal-form equivalence remain separate obligations. **Proved** for the concrete ordered field; build and axiom audit pass. |
| `found:eq:mulcut` for canonical sign options | `Surreal.Foundations.SignSequence.mulOption`, `mul_sub_mulOption`, the four option-bound lemmas, `mulLeft`, `mulRight`, `mul_options_separated`, `mulCut`, `mulCut_realized`, `mul_eq_cut` in [SignSequenceMultiplication.lean](../Surreal/Foundations/SignSequenceMultiplication.lean) | The transported field product is exactly the simplest value of the genetic product cut. Left options pair left with left or right with right; right options pair opposite sides. The rectangle identity factors the difference from the product into two option gaps, proving every strict bound and separation. Shrinking the four product families keeps both cut indices in the lower universe. Exact equality follows by matching the upstream raw-game multiplication formula through the proved cut/arithmetic bridge, not by treating every separator as the cut value. The arbitrary-presentation formula is proved below. General multiplicative birthday bounds remain separate. **Proved** for the concrete sign field; build and axiom audit pass. |
| `found:eq:mulcut` for arbitrary small factor presentations | `Surreal.Foundations.SignSequence.productCut`, `productCut_realizes_iff`, `productCut_realized`, `productCut_realizes_mulCut`, `cut_productCut`, `productCut_isPrefix_of_realizes` in [SignSequenceProductCuts.lean](../Surreal/Foundations/SignSequenceProductCuts.lean) | Conway multiplication holds for any two small separated cut presentations, including redundant options. Monotonicity of the rectangle expression transfers canonical-option cofinality to the four product families. Mutual prefix simplicity identifies their cut with the existing field product; a separator is not assumed equal to the simplest value. Every cut index stays in the lower universe. **Proved**; build and axiom audit pass. |
| Rational embeddings and non-Archimedean scales; halving proof of `found:prop:incomplete` | `Surreal.Foundations.SignSequence.rationalRingHom`, `rationalOrderEmbedding`, `toSurreal_ratCast`, `ratCast_lt_omega0`, `not_archimedean`, `natCast_lt_half_of_mem_upperBounds`, `half_mem_upperBounds_natCast`, `natCast_range_no_isLUB_by_halving`, `inv_omega0_pos`, `inv_omega0_lt_one_div_natCast`, `inv_omega0_lt_ratCast` in [SignSequenceRationals.lean](../Surreal/Foundations/SignSequenceRationals.lean) | Native rational casts preserve the field and order and agree across the sign/game equivalence. The concrete all-plus omega dominates every rational and refutes the native Archimedean property. Its reciprocal is positive and below every positive rational; reciprocal-natural statements retain the positive-index guard. Any upper bound of the natural range can be halved to a strictly smaller upper bound, completing the second source argument. No real-closedness or Hahn identification is assumed. **Proved** for these concrete embeddings, scale and incompleteness assertions; build and axiom audit pass. |
| `found:rem:ordinals` | `Surreal.Foundations.SignSequence.toIGame_ofOrdinal`, `toSurreal_ofOrdinal`, `ofOrdinal_natural_add`, `ofOrdinal_natural_mul`, `naturalOrdinalRingHom`, `ofOrdinal_add_one`, `one_add_ofOrdinal_omega0`, `ofOrdinal_one_add_omega0_ne`, `not_ofOrdinal_preserves_ordinal_add` in [SignSequenceOrdinals.lean](../Surreal/Foundations/SignSequenceOrdinals.lean) | All-plus sign sequences agree literally with upstream ordinal raw games. Their arithmetic therefore agrees with the natural sum and product on the explicit `NatOrdinal` wrapper, which is an ordered semiring embedded into the sign field. Ordinary ordinal addition is kept separate: the field sum `1 + omega` is the successor of omega, while embedding the ordinary ordinal sum gives omega. No arithmetic instance on `Ordinal` is changed. **Proved**; build and axiom audit pass. |
| Ordinary-real coefficient embedding prerequisite for `found:eq:normalform` and `found:sub:hahnworkspace`; real-scale distinction in `found:sub:modulus` | `Surreal.Foundations.SignSequence.ofReal`, `realOrderEmbedding`, `toSurreal_ofReal`, arithmetic/cast compatibility, `ofReal_lt_omega0`, `omega0_not_mem_range_ofReal`, `inv_omega0_lt_ofReal`, `exists_pos_lt_all_pos_ofReal` in [SignSequenceReal.lean](../Surreal/Foundations/SignSequenceReal.lean) | The upstream dyadic Dedekind-cut embedding of ordinary reals composes with the proved sign/game field equivalence to give an actual ordered real-field embedding, compatible with natural, integer, rational and dyadic values. Omega exceeds every embedded real, and its positive reciprocal lies below every positive embedded real. This supplies the coefficient subfield and the explicit distinction between ordinary reals and surreal scales; it does not construct Hahn evaluation, a normal form, or a real-valued modulus. **Prerequisites proved**; build and axiom audit pass. |
| Actual real-coordinate standard part for `a:eq:st` | `Surreal.Foundations.SignSequence.IsFinite`, `IsInfinitesimal`, natural/real bound equivalences, `standardPartHom`, `standardPartHom_surjective`, `infinitesimalIdeal_eq_maximalIdeal`, `standardPartQuotientEquiv`, `existsUnique_real_infinitesimal_decomposition` in [SignSequenceStandardPart.lean](../Surreal/Foundations/SignSequenceStandardPart.lean) | Mathlib’s native Archimedean valuation ring on the actual ordered sign field has residue field `ℝ` through the constructed ordinary-real embedding. Finiteness means an absolute bound by some natural; infinitesimality means an absolute bound by every positive reciprocal natural, equivalently every positive ordinary real. Standard part is an ordered ring homomorphism on finite elements, with native maximal infinitesimal kernel and a unique real-plus-infinitesimal decomposition. Zero is included in the ideal; algebraic laws retain finite-domain guards. No Hahn coefficient identification is assumed. **Proved**; build and axiom audit pass. |
| Real-coordinate clopen and separation clauses of `a:prop:clopen` | `Surreal.Foundations.SignSequence.isClopen_setOf_isFinite`, `isClopen_setOf_isInfinitesimal`, `isClopen_monad`, `isClopen_affine_finite`, `isClopen_affine_infinitesimal`, `affine_infinitesimals_eq`, `exists_isClopen_separating`, `signSequenceTotallySeparatedSpace` in [SignSequenceStandardPartTopology.lean](../Surreal/Foundations/SignSequenceStandardPartTopology.lean) | A positive actual infinitesimal gives a neighborhood inside the infinitesimal additive subgroup, making it and the finite subgroup clopen. Every nonzero affine image is clopen, including monads centered at infinite elements. Scaled monads separate every pair of distinct sign-field elements, supplying native total separatedness and disconnectedness while retaining the existing topology. The full surcomplex proposition is proved below. **Proved** for these scalar clauses; build and axiom audit pass. |
| Actual monomial and leading-data prerequisites of `found:eq:normalform`, `found:sub:hahnworkspace` | `Surreal.Foundations.SignSequence.toSurrealOrderRingIso`, Archimedean comparison transport, `omegaPower`, its strict order and exponent laws, `leadingExponent`, `leadingCoeff`, `leadingCoeff_eq_standardPart`, `finite_div_omegaPower_iff`, `infinitesimal_div_omegaPower_iff`, `standardPart_div_omegaPower_ne_zero_iff` in [SignSequenceMonomials.lean](../Surreal/Foundations/SignSequenceMonomials.lean) | The pinned Conway omega-map and logarithm transport through the actual ordered field equivalence. A nonzero element has a unique leading growth exponent and nonzero real coefficient, with normalized finite part having nonzero standard part. Scaling by `omegaPower a` is finite exactly when the growth exponent is at most `a`, and has nonzero standard part exactly at equality. The exponent at zero is a total junk value, so comparison and multiplicative criteria retain their nonzero guards. The source convention is `t^a = omegaPower (-a)`. No infinite normal form or strong evaluation is asserted. **Prerequisites proved**; build and axiom audit pass. |
| Finite monomial-scaling prerequisite for `found:sub:realclosed` | `Surreal.Foundations.SignSequence.finite_div_omegaPower_pow_iff`, `standardPart_div_omegaPower_pow_ne_zero_iff`, `exists_monomial_normalization`, `exists_monomial_finite_scaling`, `exists_pos_coefficient_scaling`, `exists_lowerCoeff_monomial_normalization` in [SignSequencePolynomialScaling.lean](../Surreal/Foundations/SignSequencePolynomialScaling.lean) | Taking the maximum of finitely many nonzero coefficients’ leading exponents divided by positive natural weights gives an actual positive monomial scale. Every weighted coefficient is finite and at least one has nonzero real standard part. Weights `n-j` specialize the theorem to all lower coefficients of a monic degree-`n` polynomial. The finiteness-only result includes all-zero and empty families; the attained nonzero residue explicitly requires a nonzero coefficient. The polynomial change of variable and ordinary-real reduction factorization are constructed below; the infinite factor lift remains separate. **Prerequisite proved**; build and axiom audit pass. |
| Polynomial translation and real residue factorization prerequisites of `found:sub:realclosed` | `Surreal.FinitePolynomial.coeff_taylor_pred_natDegree`, `monicNormalize`, `depress`, `coeff_depress_pred_eq_zero`, explicit root/translation identities, `exists_monic_depressed` in [PolynomialDepression.lean](../Surreal/Algebra/PolynomialDepression.lean); `depressed_ne_linear_pow`, `real_monic_odd_exists_root`, `real_exists_coprime_monic_factors`, `real_depressed_odd_coprime_factorization` in [RealPolynomialFactors.lean](../Surreal/Algebra/RealPolynomialFactors.lean) | Leading-coefficient normalization and Taylor translation turn any nonzero positive-degree polynomial over a characteristic-zero field into a monic depressed polynomial of the same degree, with equivalent root existence. A nontrivial depressed odd-degree ordinary-real polynomial has coprime monic factors of positive degree, one of odd degree strictly below the original. The proof extracts the full multiplicity of a real root supplied by Mathlib’s real intermediate-value consequences and uses degree parity. It neither assumes nor proves surreal root existence. **Prerequisites proved**; build and axiom audit pass. |
| Actual polynomial scaling and standard-part reduction for `found:sub:realclosed` | `Surreal.Foundations.SignSequence.scalePolynomial`, coefficient and degree formulas, `scalePolynomial_monic`, `scalePolynomial_depressed`, `isRoot_scalePolynomial_iff`, `scalePolynomial_reconstruct`, `finitePolynomial`, `reducePolynomial`, `exists_scalePolynomial_finite`, `exists_monic_depressed_reduction` in [SignSequencePolynomialNormalization.lean](../Surreal/Foundations/SignSequencePolynomialNormalization.lean) | The actual transformation is `Q = C((t^n)⁻¹) * P.comp(C t * X)`, with lower coefficients `P_j / t^(n-j)` and explicit inverse transformation and root pullback. A monomial scale makes all coefficients finite. The resulting polynomial over the genuine finite-element ring reduces via standard part to an ordinary-real polynomial preserving monicity, degree and depression. For `P ≠ X^n`, a nonzero lower residue ensures the reduction is also not a pure monomial. Coprime factor lifting and surreal root existence remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Complete finite preparation of the odd-degree-root induction in `found:sub:realclosed` | `Surreal.Foundations.SignSequence.scalePolynomial_depress_eq`, `isRoot_scalePolynomial_depress_iff`, `explicit_root_or_coprime_residue_preparation` in [SignSequenceRealClosedReduction.lean](../Surreal/Foundations/SignSequenceRealClosedReduction.lean) | Every monic odd-degree polynomial over the actual sign field either has the explicit root given by the negative depression shift, or admits a specified positive monomial scaling and translation whose finite standard-part reduction has coprime monic real factors. One factor has positive odd degree strictly below the original, and their degrees sum to the original degree. The exact transformed polynomial and affine root pullback are included. Lifting these residue factors inside the sign field remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Actual real-field valuation prerequisites of `a:eq:valuation` | `Surreal.Foundations.SignSequence.valuation`, `valuation_isEquiv_archimedean`, arithmetic/order formulas, `isFinite_iff_valuation_nonneg`, `isInfinitesimal_iff_valuation_pos`, `tMonomial`, `valuation_tMonomial`, `valuation_surjective`, `abs_lt_omegaPower_one_of_finite` in [SignSequenceValuation.lean](../Surreal/Foundations/SignSequenceValuation.lean) | Assigning zero infinity and nonzero elements minus their growth exponent gives a native additive valuation valued in `WithTop SignSequence`. It is equivalent to the native Archimedean valuation. The monomial convention is `t^a = omegaPower(-a)` and every surreal exponent occurs; no value-group truncation is imposed. Finiteness and infinitesimality agree with the already proved predicates. Identification with least support exponents of infinite Hahn normal forms remains pending. **Proved** for the actual valuation structure and these formulas; build and axiom audit pass. |
| Birthday correspondence and minimal-representative clauses in `found:sub:signs` and `found:sub:package` | `Surreal.Foundations.SignSequence.birthday_toIGame`, `numericGameSignCut`, `cut_numericGameSignCut`, `birthday_orderIso_symm_mk_le`, `birthday_le_of_toSurreal_eq_mk`, `toIGame_birthday_minimal` in [SignSequenceGameBirthday.lean](../Surreal/Foundations/SignSequenceGameBirthday.lean) | The canonical raw game's birthday is exactly the ordinal sign length. Passing from any numeric game to its sign representative never increases birthday, so the canonical game attains the minimum among all numeric representatives. The proof recursively uses small move cuts and the existing cut birthday bound. It does not identify birthday precedence with prefix simplicity. Quotient-level birthday APIs and arithmetic birthday estimates remain separate. **Proved** for the canonical and minimum-birthday assertions; build and axiom audit pass. |
| `lem:add` in the Laurent-birthday report; `found:eq:natsum` and `found:sub:recursionmeasure` | `Surreal.Foundations.SignSequence.birthday_add_le_natural`, `birthday_sub_le_natural`, `birthday_finset_sum_le`, `birthday_nsmul_le`, `pairBirthday`, `pairBirthday_lt_of_pairSimpler`, `pairSimpler_wellFounded_by_birthday`, `birthday_add_ofOrdinal`, `birthday_mul_ofOrdinal` in [SignSequenceBirthdayArithmetic.lean](../Surreal/Foundations/SignSequenceBirthdayArithmetic.lean), together with `birthday_neg` | Canonicalization of the raw game sum proves the natural-sum bound for actual sign addition, including arbitrary finite sums and finite multiples. Negation preserves sign length. The natural-sum measure strictly decreases when either coordinate becomes a proper sign prefix, giving a separate measured well-foundedness proof. On all-plus ordinal signs, both additive and multiplicative birthday bounds are equalities. Natural operations are explicitly those of `NatOrdinal`; this does not prove the general birthday-product conjecture. **Proved** for the full additive lemma and these measure/special-case assertions; build and axiom audit pass. |
| Finite-birthday cutoff in `found:sub:cutoffs` | `Surreal.Foundations.SignSequence.short_toIGame_iff`, `birthday_dyadicCast_lt_omega0`, `birthday_lt_omega0_iff_dyadic`, `dyadicRingHom`, `finiteBirthdaySubring`, `mem_finiteBirthdaySubring`, `birthday_add_lt_omega0`, `birthday_mul_lt_omega0`, `three_finite_birthday_inverse_not`, `not_exists_subfield_finite_birthday` in [SignSequenceDyadics.lean](../Surreal/Foundations/SignSequenceDyadics.lean) | A sign sequence has birthday below omega exactly when it is the embedded value of a dyadic rational. This uses the proved canonical birthday bridge and the upstream short numeric-game classification. These elements form a subring under the actual field operations. Three has finite birthday, while its reciprocal does not, so no ambient subfield has exactly this carrier. The exact finite dyadic birthday formula is proved below. **Proved** for the finite-cutoff classification and closure obstruction; build and axiom audit pass. |
| Non-dyadic real birthday assertions preceding `eq:realbirth` and `eq:dyadic-birthday`; prerequisite for `lem:realproduct` | `Surreal.Foundations.SignSequence.real_toIGame_birthday_le_omega0`, `birthday_ofReal_le_omega0`, `birthday_ofReal_lt_omega0_iff`, `birthday_ofReal_eq_omega0_of_not_dyadic`, `birthday_ofReal_eq_omega0_iff`, `birthday_one_third_eq_omega0` in [SignSequenceRealBirthday.lean](../Surreal/Foundations/SignSequenceRealBirthday.lean) | Every ordinary real has sign birthday at most omega: its raw dyadic Dedekind cut has short options, and canonicalization never increases birthday. It has finite birthday exactly when it is dyadic, and birthday exactly omega otherwise, including the explicit one-third example. These are concrete assertions about the constructed real embedding. The exact finite dyadic birthday formula and full real-product birthday inequality are proved below. **Proved** for the stated bounds and characterizations; build and axiom audit pass. |
| Exact finite formulas `eq:realbirth` and `eq:dyadic-birthday` | `Surreal.Foundations.DyadicBirthdayArithmetic.height`, `height_of_den_eq_one`, `max_height_lower_upper_add_one` in [DyadicBirthdayArithmetic.lean](../Surreal/Foundations/DyadicBirthdayArithmetic.lean); `SignSequence.birthday_dyadicCast_eq_game`, `birthday_dyadicCast_eq_max`, `dyadic_game_birthday_minimal`, `birthday_intCast`, `birthday_dyadicCast_formula`, `birthday_dyadicCast_of_den_eq_two_pow`, `birthday_ofReal_dyadic_formula` in [SignSequenceDyadicBirthday.lean](../Surreal/Foundations/SignSequenceDyadicBirthday.lean) | A dyadic with reduced denominator `2^k` has actual sign birthday `ceil(abs(q)) + k`, including negative values and zero. The arithmetic recurrence uses the reduced denominator and natural ceiling of the absolute rational value. Neighbor-cut prefix arguments and denominator induction independently prove that the native dyadic game has exactly the canonical sign birthday; equivalence alone is not used to identify raw birthdays. Proven arithmetic helpers are adapted with attribution from the recorded upstream revision, without importing its incomplete birthday module or enlarging the vendored dependency closure. **Proved** for the full formulas and the constructed ordinary-real embedding; build and axiom audit pass. |
| `lem:realproduct` in the Laurent-birthday report | `Surreal.Foundations.DyadicBirthdayArithmetic.log_den_mul_le`, `ceil_abs_mul_le`, `height_mul_le` in [DyadicBirthdayProduct.lean](../Surreal/Foundations/DyadicBirthdayProduct.lean); `SignSequence.birthday_dyadicCast_mul_le_natural`, `birthday_ofReal_mul_le_natural`, `birthday_ofReal_mul_le` in [SignSequenceRealProductBirthday.lean](../Surreal/Foundations/SignSequenceRealProductBirthday.lean) | For every pair of ordinary reals embedded in the actual sign field, the product birthday is at most the Hessenberg natural product of their birthdays. The dyadic case uses the exact finite formula, submultiplicativity of the absolute-value ceiling, and subadditivity of the reduced-denominator exponent. A nondyadic factor has birthday omega, and the real product has birthday at most omega. Zero factors are handled separately. This proves the entire real-scalar lemma, not the conjecture for arbitrary surreal factors. **Proved**; build and axiom audit pass. |
| `found:eq:pairmul`, `found:eq:conj`, `found:eq:pairinv`; part of `found:prop:complex` | `Surreal.Complexify`, `Complexify.mul_re`, `mul_im`, `I_sq`, `conj_conj`, `conj_mul`, `noRootNegOne`, `inv_eq`, `inv_re`, `inv_im` in [Complexify.lean](../Surreal/Algebra/Complexify.lean) | Mathlib quadratic algebra and its field instance over an arbitrary ordered field. The concrete sign-field specialization is proved below; algebraic closedness remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Concrete pair field in `found:sub:pairs`; `found:eq:pairadd`, `found:eq:pairmul`, `found:eq:conj`, `found:eq:pairinv`; field and carrier clauses of `found:prop:complex` | `Surreal.Surcomplex`, `Surcomplex.ofReal`, `ofReal_injective`, `I_sq`, `add_eq`, `mul_eq`, `conj`, `conj_eq`, `conj_conj`, `re_add_im_mul_I`, `normSq_pos`, `normSq_mul`, `mul_conj`, `inv_eq`, `finrank_eq_two`, `not_small` in [Surcomplex/Basic.lean](../Surreal/Surcomplex/Basic.lean) | The concrete surcomplex carrier is the existing quadratic algebra over the constructed sign field, inheriting its proved field instance. Its coordinate addition, multiplication, conjugation and inverse formulas are instantiated without additional premises; the inverse denominator is positive for every nonzero pair. Norm squares take values in the sign field, and every pair decomposes as real plus imaginary parts. The extension has dimension two and is not lower-universe-small because its injective real axis already contains the entire sign carrier. Its fine topology and actual surreal-valued modulus are constructed below; algebraic closedness remains pending. **Proved** for these concrete field, coordinate and size clauses; build and axiom audit pass. |
| Surcomplex clauses of `found:thm:discrete`, fine-ball topology and no-isolated-points sharpness in `found:sub:discrete` | `Surreal.Surcomplex.coordinateUniformEquiv`, `surcomplexIsUniformAddGroup`, `fineBall`, `isOpen_fineBall`, `nhds_hasBasis_fineBall`, `uniformity_hasBasis_normSq_sub`, `isClosed_of_small`, `isDiscrete_of_small`, `tendsto_nhds_iff_eventually_eq_of_small_range`, `eventually_constant_of_cauchy_small_range`, `cauchy_map_iff_eventually_constant`, `punctured_nhds_neBot`, `not_discreteTopology` in [Surcomplex/FineTopology.lean](../Surreal/Surcomplex/FineTopology.lean) | The actual pair field carries the product of the native sign uniformities, compatible with its existing addition. Positive surreal squared-radius balls `normSq (z-a) < r²` give exactly its neighborhood and entourage bases. Every lower-universe-small subset is closed and discrete. Small-range convergent nets are eventually their limits, and small-range Cauchy nets are eventually an attained value; small index types imply these hypotheses. The Cauchy iff retains nontriviality of the filter. Every ball contains the distinct point `a + r/2` along the real axis, so the full carrier has no isolated points. No real-valued metric, square-root or real-closedness premise is used. **Proved** in squared-radius form; the actual modulus identification is proved below. Build and axiom audit pass. |
| Fine-topological compatibility of `found:sub:pairs`; surcomplex form of `found:ex:largerindex` | `Surreal.Surcomplex.surcomplexT2Space`, `continuous_mul_coordinates`, `continuousAt_inv_of_ne_zero`, `surcomplexIsTopologicalDivisionRing`, `conjUniformEquiv`, `conjHomeomorph`, `uniformContinuous_ofReal`, `positiveRealAxisNet_tendsto_zero`, `positiveRealAxisNet_cauchy`, `positiveRealAxisNet_not_eventually_constant`, `positiveRealAxisNet_index_not_small`, `positiveRealAxisNet_range_not_small` in [Surcomplex/TopologicalField.lean](../Surreal/Surcomplex/TopologicalField.lean) | The existing surcomplex field and fine topology form a Hausdorff topological division ring. Polynomial coordinate formulas give joint multiplication continuity; the nonzero norm-square denominator gives inverse continuity away from zero. Conjugation is a uniform equivalence, and the surreal real-axis inclusion is uniformly continuous. The positive-radius net on that axis is Cauchy and converges to zero but is never zero or eventually constant. Its index and range both fail lower-universe smallness. The original field, uniformity and topology are retained, with no square-root or real-closedness assumptions. **Proved** for these concrete assertions; build and axiom audit pass. |
| Order and algebraic-closedness obstructions in `found:sub:realclosed` | `Surreal.eval_X_sq_add_one_pos`, `not_isRoot_X_sq_add_one`, `orderedField_not_isAlgClosed`, `Foundations.SignSequence.not_isAlgClosed`, `Surcomplex.no_compatible_linearOrder` in [Surcomplex/OrderObstructions.lean](../Surreal/Surcomplex/OrderObstructions.lean) | Over every ordered field, the polynomial `X² + 1` is positive everywhere and has no root, excluding algebraic closedness. This applies to the actual sign field. Every proposed linear order on the existing surcomplex field fails ordered-ring compatibility because its imaginary unit squares to minus one. Neither argument assumes or proves real closedness of the sign field or algebraic closedness of the surcomplex field. **Proved**; build and axiom audit pass. |
| `found:eq:gram`, `found:eq:cauchyschwarz`, `trigonometry:eq:gram` | `Surreal.Complexify.gram_identity`, `cauchy_schwarz_sq`, `normSq_mul`, `mul_conj` | Generic algebraic identities and their ordered-field consequence. The scalar formula is proved independently of any surreal representation. **Prerequisites proved**; build and axiom audit pass. |
| `a:prop:triangle` | `Surreal.Complexify.modulus_mul`, `modulus_add_le`, `abs_re_le_modulus`, `abs_im_le_modulus`, `inv_eq_modulus` in [Modulus.lean](../Surreal/Algebra/Modulus.lean) | The stated identities over an ordered field with the proved nonnegative-square-root property, with modulus valued in that field. The concrete surcomplex interpretation is proved below. **Prerequisites proved**; build and axiom audit pass. |
| Nonnegative square-root obligation of `found:sub:realclosed` and `found:sub:modulus` | `Surreal.Foundations.SignSequence.squareRootTransition`, `squareRootTransition_sq_sub`, `IsSquareRootBracket`, `squareRootOptions`, `squareRootOptionCut`, `squareRootOptionCut_product_realized`, `squareRootOptionCut_sq_isPrefix`, `exists_nonneg_sq`, `existsUnique_nonneg_sq`, `sqrt`, `sqrt_sq`, `sqrt_sq_eq_abs` in [SignSequenceRoots.lean](../Surreal/Foundations/SignSequenceRoots.lean) | Every nonnegative element of the actual sign field has a unique nonnegative square root. Simplicity induction supplies roots of nonnegative canonical options. A countable closure under the rational transition `(x+a*b)/(a+b)` preserves square bracketing and lower-universe smallness; zero denominators are excluded and the all-zero product-option case is handled separately. Arbitrary-presentation multiplication proves one prefix direction for the candidate square, and the seed roots prove the reverse direction. A total square-root function is zero on negative inputs. This constructs roots without topological convergence, a Hahn bridge, or a real-closedness assumption. Odd-degree polynomial roots and real closedness remain pending. **Proved** for square roots; build and axiom audit pass. |
| Full `a:prop:triangle`; `found:sub:modulus`; concrete area/inequality clauses of `trigonometry:thm:heron` and `trigonometry:thm:ptolemy` | `Surreal.HasNonnegSquareRoots` in [OrderedSquareRoots.lean](../Surreal/Algebra/OrderedSquareRoots.lean); `SignSequence.signSequenceHasNonnegSquareRoots`, `Surcomplex.modulus`, `modulus_sq`, `modulus_mul`, `modulus_add_le`, coordinate bounds, `inv_eq_modulus`, `modulus_add_eq_iff_pos_quotient`, `heron`, `ptolemy`, `fineBall_eq_modulus`, `nhds_hasBasis_modulus`, `uniformity_hasBasis_modulus_sub`, `abs_sub_modulus_le`, `continuous_modulus` in [Surcomplex/Modulus.lean](../Surreal/Surcomplex/Modulus.lean) | The proved sign-field square roots instantiate the existing generic geometry through an explicit square-root property, automatically satisfied by real closed fields but strictly sufficient here without asserting real closedness. The actual surcomplex modulus is surreal-valued and satisfies every identity and inverse clause of the analysis proposition. Its positive-radius balls generate exactly the native fine topology and Cauchy uniformity; it obeys the reverse triangle estimate and is continuous. Heron, Ptolemy inequality, and the nonzero positive-quotient triangle-equality criterion apply to the concrete carrier. Angle/radius clauses, cyclic Ptolemy equality, and algebraic closedness remain pending. **Proved** for the full modulus proposition and these exact geometric/topological clauses; build and axiom audit pass. |
| Actual finite-ring, maximal-ideal, residue and decomposition clauses of `a:eq:st` | `Surreal.Surcomplex.IsFinite`, `IsInfinitesimal`, modulus-bound equivalences, `finiteSubring`, `finiteValuationSubring`, `standardPartHom`, `standardPartHom_surjective`, `standardPart_modulus`, `infinitesimalIdeal_isMaximal`, `standardPartQuotientEquiv`, `existsUnique_complex_infinitesimal_decomposition` in [Surcomplex/StandardPart.lean](../Surreal/Surcomplex/StandardPart.lean) | On the actual surcomplex field, coordinatewise standard part is a surjective ring homomorphism from the finite valuation subring to ordinary `ℂ`. Finiteness is exactly a natural modulus bound and infinitesimality exactly every positive reciprocal-natural bound. The kernel is the maximal infinitesimal ideal, its quotient is `ℂ`, and both terms of the ordinary-complex plus infinitesimal decomposition are unique. Standard part commutes with conjugation and sends the modulus of a finite element to the ordinary norm of its standard part. Identification with Hahn exponents and coefficient-zero extraction remains pending. **Proved** for these actual algebraic and modulus assertions; build and axiom audit pass. |
| Ordinary complex coefficient embedding for `a:eq:normal` and `a:eq:st` | `Surreal.Surcomplex.ofComplex`, `ofComplex_injective`, coordinate and conjugation compatibility, `normSq_ofComplex`, `modulus_ofComplex` in [ComplexEmbedding.lean](../Surreal/Surcomplex/ComplexEmbedding.lean) | Applies the actual ordered real embedding to both ordinary complex coordinates, giving an injective ring homomorphism into the constructed surcomplex field. Its actual modulus is the embedded ordinary complex norm. This supplies constants without identifying the ordinary and fine topologies or assuming algebraic closedness. **Proved**; build and axiom audit pass. |
| `found:cor:nopaths`, `a:cor:nopath` | `Surreal.Surcomplex.eq_of_isPreconnected_of_small_range`, `eq_of_isPreconnected`, `eq_of_continuous`, `eq_of_continuousOn_Icc` in [NoPaths.lean](../Surreal/Surcomplex/NoPaths.lean) | A fine-continuous map with permitted-small range is constant on every preconnected subset of its domain. Small index types suffice, including every ordinary real interval. This reuses Mathlib connectedness and the proved small-range discreteness of the actual fine topology, without requiring the whole surcomplex carrier to be small or discrete. **Proved**; build and axiom audit pass. |
| Arithmetic and modulus identities of `a:eq:valuation`; `a:lem:valbound` | `Surreal.Surcomplex.valuation`, `valuation_eq_modulus`, `valuation_mul`, `min_valuation_le_add`, `valuation_eq_min_coordinates`, `valuationSubring_eq_finiteValuationSubring`, finite/infinitesimal valuation characterizations, `tMonomial`, `valuation_surjective`, `isFinite_div_tMonomial_iff`, `isInfinitesimal_div_tMonomial_iff`, `modulus_lt_tMonomial_sub_one` in [Valuation.lean](../Surreal/Surcomplex/Valuation.lean) | Valuation of the actual modulus defines an additive surcomplex valuation with actual surreal values and infinity at zero. It equals the minimum of the coordinate valuations, restricts to the sign-field valuation, is invariant under conjugation, and has value zero on nonzero ordinary constants. Its valuation subring is exactly the existing finite ring. Scaling by `t^a` translates valuation bounds to finiteness or infinitesimality. Every bound `v(z) ≥ β` implies the source estimate `modulus(z) < t^(β-1)`, including zero. Infinite normal-form support identification remains separate. **Proved** for the actual valuation formulas and full bound lemma; build and axiom audit pass. |
| Actual leading-term decomposition and `a:eq:modulusleading` | `Surreal.Surcomplex.leadingExponent`, `normalized`, `leadingCoeff`, `finite_normalized`, `leadingCoeff_ne_zero`, `leadingCoeffMonoidWithZeroHom`, `exists_leading_error`, `valuation_lt_sub_leadingTerm`, `exists_modulus_leading_error`, `leadingCoeff_modulus` in [Leading.lean](../Surreal/Surcomplex/Leading.lean) | Dividing by the actual leading monomial gives a finite element with nonzero complex standard part for nonzero input. This constructs a leading coefficient, proves its multiplicative/inverse/division laws, and writes the element as its monomial times a constant plus an infinitesimal. Removing the leading term strictly raises valuation. The modulus has the same monomial and the ordinary norm of the complex leading coefficient, with an infinitesimal error. Zero is handled by explicit total conventions. **Proved** for these leading-term assertions and the modulus formula; identification with all coefficients of an infinite normal form remains pending. Build and axiom audit pass. |
| Full `a:prop:clopen`; fine continuity of standard part | `Surreal.Surcomplex.isClopen_setOf_isFinite`, `isClopen_setOf_isInfinitesimal`, `isClopen_monad`, `isClopen_affine_finite`, `isClopen_affine_infinitesimal`, `surcomplexTotallySeparatedSpace`, `finite_standardPart_fiber_eq_monad`, `isClopen_standardPart_fiber`, `isLocallyConstant_standardPartHom`, `continuous_standardPartHom` in [StandardPartTopology.lean](../Surreal/Surcomplex/StandardPartTopology.lean) | Both coordinate preimages are clopen, giving the actual finite ring and infinitesimal ideal as clopen subsets of the full fine topology. Every monad and nonzero affine image is clopen, with arbitrary centers including infinite elements. Coordinate separators give total separatedness and therefore total disconnectedness. On the genuine finite domain, ordinary-complex standard part is locally constant and continuous. The existing topology and uniformity are retained. **Proved** for the full proposition and these standard-part consequences; build and axiom audit pass. |
| `a:def:halo`, `a:rem:puncture`, `a:rem:halonotball` | `Surreal.Surcomplex.halo`, `halo_eq_iUnion_monads`, `mem_halo_iff_exists`, `affine_halo_eq`, `halo_punctured`, `halo_punctured_ne_remove_zero`, `isClopen_halo`, `isClopen_affine_halo`, `unitDiskBoundaryWitness`, `halo_unitDisk_ne_fineBall` in [Halos.lean](../Surreal/Surcomplex/Halos.lean) | A halo is exactly the finite-domain standard-part preimage, equivalently the union of the corresponding constant-plus-infinitesimal monads. Every halo and every nonzero affine chart is fine-clopen, even for arbitrary ordinary subsets. Deleting an ordinary point removes the whole monad; for domains containing zero this is proved different from deleting only zero, using a nonzero actual infinitesimal. The explicit point `1 - omega⁻¹` lies in the actual fine unit ball but has standard part one, so the halo of the ordinary unit disk is not that ball. **Proved** for these definitions and assertions; build and axiom audit pass. |
| `found:lem:nometric` and the following real-metric obstruction | `Surreal.Foundations.SignSequence.exists_positive_lower_bound_of_small`, `exists_positive_lower_bound_of_countable`; `Surcomplex.exists_ball_not_refined_by_small_family`, `exists_ball_not_refined_by_countable_family`, `not_isCountablyGenerated_nhds`, `not_has_countable_nhds_basis`, `not_firstCountableTopology`, `not_pseudoMetrizableSpace`, `not_metrizableSpace` in [NoMetric.lean](../Surreal/Surcomplex/NoMetric.lean) | A positive bound below every half-radius defeats every proposed small family of fine balls; arbitrary-universe countable index types are included through their smallness. No neighborhood filter at any actual surcomplex point is countably generated: a sequence in the punctured neighborhoods would contradict eventual equality for small-index convergent nets. This rules out arbitrary countable local bases, first countability and compatible real pseudometrics or metrics. The previously proved no-isolated-point result supplies the nondiscreteness clause. **Proved**; build and axiom audit pass. |
| `found:eq:rationalcircle`; affine clauses of `trigonometry:thm:cayley` | `Surreal.Complexify.normSq_circleParam`, `circleParam_ne_neg_one`, `circleCoord_circleParam`, `circleParam_circleCoord`, `circleParam_injective`, `circleEquiv` in [Circle.lean](../Surreal/Algebra/Circle.lean) | The rational affine chart and its inverse give an equivalence over any ordered field. The projective extension and direction multiplication are mapped below. The half-angle identity and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Projective and algebraic multiplication clauses of `trigonometry:thm:cayley`, `trigonometry:eq:cayley`, `trigonometry:eq:projectiveaddition` | `Surreal.Complexify.projectiveCircleEquiv`, `projectiveCircleEquiv_mk`, `circleParam_eq_fraction`, `projective_add_pair_ne_zero`, `projectiveAdd_mk`, `circleParam_mul`, `circleParam_mul_eq_neg_one_iff`, `projectiveAdd_infty_infty` in [ProjectiveCircle.lean](../Surreal/Algebra/ProjectiveCircle.lean) | Mathlib's actual projectivization of `Fin 2 → F` is equivalent to the norm-square-one circle over any ordered field. The chart has the homogeneous quotient formula and transports direction multiplication to `[ps+qr:qs-pr]`, whose output pair is proved nonzero. The affine rule applies exactly off its zero denominator; zero denominator gives `-1`, and two points at infinity give affine zero. Associativity and commutativity are also proved. The tangent/half-angle relation, infinitesimal proximity claim and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Factorization clauses of `polynomial:thm:fta`, `polynomial:eq:factorization`, `polynomial:eq:logderivative` | `Surreal.FinitePolynomial.exists_root`, `factorization`, `factorization_grouped`, `exists_unique_factorization`, `factorization_unique`, `sum_rootMultiplicities`, `logarithmic_derivative`, `logarithmic_derivative_grouped` in [Polynomial.lean](../Surreal/Algebra/Polynomial.lean) | Root existence, unique scalar/multiset factorization, grouped multiplicities and both logarithmic-derivative formulas. Existence assumes algebraic closedness; uniqueness holds over every field. The rational identities require a nonroot evaluation point. The fixed-Hahn closedness instance and explicit factorization specialization are now constructed below; transfer to the actual surcomplex field remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Division, gcd and ideal clauses of `polynomial:thm:fta`; gcd formula in `polynomial:eq:logderivative` | `Surreal.FinitePolynomial.exists_unique_division`, `exists_monic_gcd`, `gcd_bezout`, `ideal_principal`, `ideal_pair_eq_span_gcd`, `squarefree_iff_gcd_derivative_eq_one`, `gcd_derivative_rootMultiplicity`, `gcd_derivative_eq_prod` in [PolynomialDivision.lean](../Surreal/Algebra/PolynomialDivision.lean) | Unique division, normalized monic Bézout gcds and principal ideals over every field. The squarefree criterion assumes perfectness (supplied by characteristic zero); derivative multiplicities use characteristic zero. The grouped gcd product assumes a nonzero split polynomial and does not need monicity of the input. **Prerequisites proved**; build and axiom audit pass. |
| Multiplicity and Taylor clauses of `polynomial:thm:fta` | `Surreal.FinitePolynomial.multiplicity_eq_iff_derivatives`, `multiplicity_isLeast_nonzero_derivative`, `derivative_rootMultiplicity`, `multiple_root_iff`, `taylor_coeff_eq_derivative`, `taylor_eq_sum_derivatives`, `eq_sum_derivatives`, `eval_add_eq_sum_derivatives` in [PolynomialMultiplicity.lean](../Surreal/Algebra/PolynomialMultiplicity.lean) | The least nonvanishing derivative, derivative multiplicity and finite Taylor formulas over characteristic-zero fields. The least-index characterization explicitly excludes the zero polynomial. **Prerequisites proved**; build and axiom audit pass. |
| Binary clause of `polynomial:eq:factorlinear`; prerequisite of `polynomial:thm:hensel` | `Surreal.FinitePolynomial.factorLinearMap`, `factorLinearEquiv`, `factorCorrection`, `factorCorrection_spec`, `factorCorrection_unique`, `existsUnique_bounded_factor_correction`, `mul_perturbation_eq_linearization` in [PolynomialFactorLinearization.lean](../Surreal/Algebra/PolynomialFactorLinearization.lean) | Mathlib’s Sylvester map gives the linearization `(h,k) ↦ h*q+p*k` on perturbations below the factor degrees. A unit resultant makes it a linear equivalence for coprime factors with only the first required monic, over any commutative ring. The inverse provides unique bounded corrections with exact polynomial equality, and the quadratic remainder is explicit. Constant factors and the zero ring are included. The full finite-family version and support-controlled Hahn lifting are proved below; actual surreal transfer remains pending. **Proved** for the binary finite-algebra clause; build and axiom audit pass. |
| Full finite-family isomorphism `polynomial:eq:factorlinear` | `Surreal.FinitePolynomial.factorCofactor`, `factorLinearSum`, degree bounds, `factorLinearSum_injective_on_bounds`, `existsUnique_bounded_finite_factor_correction`, `finiteFactorLinearEquiv`, `finiteFactorCorrection`, exact forward/inverse formulas and uniqueness in [PolynomialFiniteFactorLinearization.lean](../Surreal/Algebra/PolynomialFiniteFactorLinearization.lean) | For any finite family of pairwise coprime monic polynomials, the cofactor-weighted sum is a linear equivalence from individually degree-bounded corrections to polynomials below the sum of factor degrees. Binary Sylvester inverses give the corrections modulo each factor; pairwise coprimality and monic degree bounds turn the resulting divisibility into exact equality. This holds over arbitrary commutative rings and includes empty families and degree-zero factors, hence specializes to the complete ordinary-complex assertion. Full support-controlled Hahn factorization is now mapped below; transfer to the actual sign field remains pending. **Proved** for the full finite-linearization equation; build and axiom audit pass. |
| Formal-parameter stage of `polynomial:thm:hensel` and `polynomial:eq:henselrecursion` | `Surreal.FinitePolynomial.factorLiftCoeff`, `factorLiftCoeff_eq`, `factorLift_linearization`, `liftedFactors_mul`, `liftedFactors_unique`, `existsUnique_formal_factorization` in [PowerSeriesFactorLifting.lean](../Surreal/Algebra/PowerSeriesFactorLifting.lean); `polynomialSeriesEmbedding`, `polynomialOfBoundedSeries`, `liftedPolynomials_mul`, `liftedPolynomials_isCoprime`, `existsUnique_monic_factorization_over_powerSeries` in [PowerSeriesPolynomialFactorLifting.lean](../Surreal/Algebra/PowerSeriesPolynomialFactorLifting.lean) | The bounded Sylvester inverse recursively constructs binary coprime factors in a natural-number formal parameter, with exact product and uniqueness among all bounded candidates. An injective variable interchange packages the factors as actual polynomials over `PowerSeries R`. Every monic polynomial of the prescribed degree whose constant specialization is a coprime monic product has unique monic lifts of the prescribed degrees and reductions. The constructed lifts remain coprime, using a unit resultant. Coefficient rings may have zero divisors; exact-degree existence states nontriviality explicitly. This proves the formal-parameter case, not arbitrary Hahn-support lifting or evaluation in the sign field. **Prerequisites proved**; build and axiom audit pass. |
| Multivariate formal stage of `polynomial:thm:hensel`, `polynomial:eq:henselrecursion` | `Surreal.FinitePolynomial.mvFactorLiftCoeff`, `mvFactorLift_linearization`, `existsUnique_mvFormal_factorization` in [MvPowerSeriesFactorLifting.lean](../Surreal/Algebra/MvPowerSeriesFactorLifting.lean); `polynomialMvSeriesEmbedding`, `polynomialOfBoundedMvSeries`, `existsUnique_monic_factorization_over_mvPowerSeries` in [MvPowerSeriesPolynomialFactorLifting.lean](../Surreal/Algebra/MvPowerSeriesPolynomialFactorLifting.lean); `universalMonicPerturbation` and its specialization formulas in [PolynomialUniversalPerturbation.lean](../Surreal/Algebra/PolynomialUniversalPerturbation.lean) | Recursion on total multiindex degree constructs unique bounded binary formal factors, with finite antidiagonals at every step. The parameter type may be arbitrary, including empty. Uniform polynomial-degree bounds give actual polynomials over the multivariate power-series ring. Any monic input with a coprime monic constant specialization has unique monic coprime factors of the prescribed degrees and reductions; nontriviality is explicit for exact-degree existence. A universal perturbation with one parameter for each lower coefficient specializes to every polynomial error below the leading degree. No Hahn evaluation is assumed in these formal statements. **Prerequisites proved**; build and axiom audit pass. |
| Full Hahn-field `polynomial:thm:hensel`, `polynomial:eq:henselfactor` | `Surreal.FinitePolynomial.BinaryMonicFactorLifting` and finite-family reduction theorems in [PolynomialFiniteFactorLifting.lean](../Surreal/Algebra/PolynomialFiniteFactorLifting.lean); `Surreal.HahnSeries.exists_monic_factorization_with_support_of_standardPart`, `existsUnique_monic_factorization_of_standardPart`, `existsUnique_monic_finite_factorization_of_standardPart`, ambient coefficient/error forms in [PolynomialFactorLifting.lean](../Surreal/HahnSeries/PolynomialFactorLifting.lean); `support_finite_factor_coeff_subset_residueErrorSupport`, `degree_factor_correction_lt`, `support_finite_factor_correction_subset`, `existsUnique_monic_finite_factorization_with_support` in [PolynomialFiniteFactorSupport.lean](../Surreal/HahnSeries/PolynomialFiniteFactorSupport.lean) | Every finite coprime monic residue factorization of a monic polynomial over the nonnegative-order Hahn ring lifts uniquely to monic factors of the same degrees. Universal formal factors are evaluated at the actual finitely many coefficient errors, supplying existence without an assumed lift or summation map. Every correction has lower polynomial degree, positive-order coefficients and support inside the original error monoid with zero removed. Binary comparison against the original polynomial gives the common support bound for every factor; uniqueness also holds among candidates without that bound. Coprimeness already holds over the valuation ring, hence over the ambient field. Empty families, constant factors and arbitrary characteristic are allowed; no divisibility or rank restriction on the exponent group is used. **Proved** for the full theorem in its explicitly fixed Hahn workspace. Transfer to the actual surcomplex carrier remains a separate bridge. Build and axiom audit pass. |
| Full Hahn-field `polynomial:cor:simpleroot`, `polynomial:eq:firstrootcorrection` | `Surreal.HahnSeries.exists_supported_root_of_simple_standardPart`, `existsUnique_infinitesimal_root_correction`, `existsUnique_supported_root_correction` in [PolynomialSimpleRootLifting.lean](../Surreal/HahnSeries/PolynomialSimpleRootLifting.lean); `coeff_eval_constant`, `first_root_correction_linear_identity`, `first_root_correction_coeff` in [PolynomialFirstRootCorrection.lean](../Surreal/HahnSeries/PolynomialFirstRootCorrection.lean); `orderTop_supported_correction_ge`, `exists_least_coefficient_support`, `existsUnique_supported_root_correction_with_coefficients`, `existsUnique_supported_root_correction_at_least_error_exponent` in [PolynomialSimpleRootCorrection.lean](../Surreal/HahnSeries/PolynomialSimpleRootCorrection.lean) | Every simple residue root lifts uniquely with positive correction support in the original error monoid minus zero. A common nonnegative lower bound for the input supports bounds each nonzero element of their additive closure. At any positive common lower bound, Taylor expansion eliminates the quadratic terms and gives the stated first-coefficient formula, including cancellation. The least input exponent exists for every nonzero error polynomial; zero error needs no artificial minimum. Evaluation of the coefficient polynomial identifies the numerator with the source's `E_e(c)`. Uniqueness compares all positive-order root corrections. No algebraic closedness, divisibility or Archimedean hypothesis is used. **Proved** for the full fixed-Hahn corollary; actual surreal transfer remains pending. Build and axiom audit pass. |
| Full Hahn-field `polynomial:cor:clusterfactor` | `Surreal.HahnSeries.isRoot_cluster_factor_iff`, `isRoot_map_cluster_factor_iff`, `existsUnique_cluster_factors`, `residueRootSet`, `residueMultiplicity`, `existsUnique_canonical_cluster_factors_of_splits`, `existsUnique_complex_cluster_factors` in [PolynomialClusterFactors.lean](../Surreal/HahnSeries/PolynomialClusterFactors.lean) | The actual distinct residue roots index unique monic cluster factors of their ordinary multiplicity degrees, with exact product, pairwise coprimeness and correction support in the original error monoid minus zero. A factor's ambient Hahn roots are exactly the original roots with its prescribed standard part: the existing monic-root valuation bound proves those roots finite before reduction. Splitting is required only for the ordinary residue polynomial and supplied automatically by Mathlib for complex coefficients. No Hahn algebraic-closedness or divisible-exponent assumption is used, and no individual splitting of multiple clusters is asserted. Empty root sets and constant monic inputs are included. **Proved** for the full fixed-Hahn corollary; actual surreal transfer remains pending. Build and axiom audit pass. |
| Local kernel calculation for `polynomial:thm:crt` | `Surreal.FinitePolynomial.pow_linear_dvd_iff_derivatives_vanish`, `derivative_jets_eq_iff_dvd_sub` | A jet vanishes exactly when the corresponding power of `X - a` divides the polynomial; equal jets correspond to divisibility of the difference. These include zero polynomials. **Prerequisites proved**; build and axiom audit pass. |
| Hermite interpolation clause of `polynomial:thm:crt` | `Surreal.FinitePolynomial.exists_unique_interpolation_representative`, `exists_unique_hermite_interpolant`, `exists_unique_hermite_interpolant_fin` in [PolynomialInterpolation.lean](../Surreal/Algebra/PolynomialInterpolation.lean) | Arbitrary finite derivative jets at distinct nodes determine a unique polynomial of degree below the sum of multiplicities, over a characteristic-zero field. Zero multiplicities and the empty index type are included. Other finite CRT clauses are mapped separately below. **Prerequisites proved**; build and axiom audit pass. |
| Quotient and idempotent clauses of `polynomial:thm:crt`, `polynomial:eq:finiteCRT` | `Surreal.FinitePolynomial.polynomialCRT`, `polynomialCRT_mk_derivative_jet`, `crtIdempotent`, `mk_eq_crtIdempotent_of_local_congruences`, `exists_crtIdempotent_representative`, `crtIdempotent_mul_self`, `crtIdempotent_mul_of_ne`, `sum_crtIdempotent` in [PolynomialCRT.lean](../Surreal/Algebra/PolynomialCRT.lean) | The quotient by the product of local moduli is ring-isomorphic to the product of truncated polynomial rings. Its Taylor forward map has the displayed derivative-jet formula in characteristic zero. Coordinate idempotents are orthogonal and sum to one, with bounded-degree representatives and a local-congruence criterion. Empty indices and zero multiplicities are included. Concrete representatives and the simple-root formula are mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Explicit local inverse and `PᵢCᵢ` representatives in `polynomial:thm:crt` | `Surreal.FinitePolynomial.inverseJet`, `inverseJet_eq_sum`, `node_pow_dvd_mul_inverseJet_sub_one`, `inverseJet_unique`, `interpolationCofactor_eq_div`, `interpolationCofactor_eval_ne_zero`, `inverseJetIdempotentPolynomial_degree_lt`, `mk_inverseJetIdempotentPolynomial` in [PolynomialInverseJet.lean](../Surreal/Algebra/PolynomialInverseJet.lean) | Truncating the actual reciprocal formal Taylor series gives the unique local inverse of degree below the multiplicity. The cofactor is exactly `P / Aᵢ` and is nonzero at its node. Each product `PᵢCᵢ` has degree below the total multiplicity, satisfies all local congruences, and represents the coordinate idempotent. Works over every field, including zero multiplicities. The derivative formula is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Constructive interpolant in the proof of `polynomial:thm:crt` | `Surreal.FinitePolynomial.hermiteInterpolant`, `hermiteInterpolant_local_congruences`, `hermiteInterpolant_degree_lt`, `hermiteInterpolant_unique`, `polynomialCRT_hermiteInterpolant`, `polynomialCRT_symm_mk`, `hermiteJetInterpolant_derivative`, `hermiteJetInterpolant_unique` in [PolynomialHermiteFormula.lean](../Surreal/Algebra/PolynomialHermiteFormula.lean) | The remainder modulo `P` of the explicit finite sum `∑ᵢ PᵢCᵢqᵢ` is the unique interpolant below the total-multiplicity degree bound with the prescribed polynomial residue classes. Its image under the CRT equivalence is the translated tuple, and translating local-variable representatives back gives the explicit inverse of that equivalence. Choosing the local Taylor representatives realizes the requested derivative jets in characteristic zero. Empty node sets and zero multiplicities are included. **Prerequisites proved**; build and axiom audit pass. |
| Formal reciprocal derivative formula in `polynomial:eq:inversejet` | `Surreal.FinitePolynomial.constantCoeff_iterate_powerSeries_derivative`, `reciprocalDerivativeNumerator`, `iterate_derivative_inverse_taylor`, `inverseJet_eq_sum_formal_derivatives`, `inverseJet_eq_sum_reciprocal_numerators`, `reciprocal_jet_denominator_ne_zero` in [PolynomialRationalJets.lean](../Surreal/Algebra/PolynomialRationalJets.lean) | In characteristic zero, the inverse jet coefficients are the iterated derivatives of the reciprocal Taylor series at zero divided by factorials. The repeated quotient-rule numerator recurrence is verified using Mathlib's actual formal derivative, yielding explicit coefficients `Nⱼ(a)/(q(a)^(j+1)·j!)` with nonzero denominators when `q(a) ≠ 0`. This is an algebraic local formal-series interpretation; a global `RatFunc` derivative operator and comparison with analytic derivatives are not supplied. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:lambdadef`; finite quotient prerequisites of `polynomial:thm:trace` | `Surreal.FinitePolynomial.residueFunctional`, `residueFunctional_mk`, `quotient_powerBasis_repr`, `quotient_leftMulMatrix`, `quotient_trace_eq_sum`, `quotient_norm_eq_det`, `map_monic_remainder_coeff` in [PolynomialQuotient.lean](../Surreal/Algebra/PolynomialQuotient.lean) | Uses Mathlib's `AdjoinRoot`, monic remainder and power basis over any commutative ring. Multiplication-matrix entries and trace are explicit remainder coefficients; the norm is their determinant. Coefficient maps commute with monic remainder extraction, without inverse coefficients. The universal norm/resultant identity is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Perfection and explicit dual-basis clauses of `polynomial:thm:residuepairing`, `polynomial:eq:dualbasis`, `polynomial:eq:eulerderivative` | `Surreal.FinitePolynomial.dualPolynomial`, `coeff_dualPolynomial`, `sum_X_pow_mul_dualPolynomial`, `coeff_modByMonic_X_pow_mul_dualPolynomial`, `residueFunctional_root_pow_mul_dualPolynomial` in [PolynomialResidueDual.lean](../Surreal/Algebra/PolynomialResidueDual.lean); `residuePairingEquiv`, `residuePairingEquiv_symm_apply`, `residueDualBasis`, `residueDualBasis_apply`, `quotient_repr_eq_residue` in [PolynomialResiduePairing.lean](../Surreal/Algebra/PolynomialResiduePairing.lean) | The displayed finite dual polynomials satisfy the Kronecker pairing identity and the Euler derivative sum. The pairing is a linear equivalence from the quotient to its linear dual, with an explicit finite-sum inverse; the dual vectors form an actual basis. All statements hold over arbitrary commutative rings, including zero divisors and the zero ring, with no separability or characteristic hypothesis. Degree zero is included by empty index types. Gram determinant and the inverse coefficient matrix are mapped separately below. The Gram, bivariate Bézout-kernel and Laurent-coefficient identities are mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Universal trace identity in `polynomial:thm:trace`, `polynomial:eq:traceidentity` | `Surreal.FinitePolynomial.quotient_sum_basis_mul_dual`, `quotient_trace_eq_residue_derivative`, `quotient_trace_mk_eq_coeff` in [PolynomialResiduePairing.lean](../Surreal/Algebra/PolynomialResiduePairing.lean) | Multiplication trace is exactly `λ(P′h)` over any commutative ring. For a polynomial representative it is the top coefficient of `(P′Q) %ₘ P`, with the derivative and trace both taken from Mathlib. The proof uses the explicit dual basis and finite Euler sum, so remains valid at collisions and in positive characteristic. The trace Gram factorization, universal discriminant equality and norm/resultant identities are mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Gram determinant and inverse coefficient matrix in `polynomial:thm:residuepairing`, `polynomial:eq:gramdet` | `Surreal.FinitePolynomial.residueGram`, `residueGram_entry_eq_zero`, `residueGram_entry_eq_one`, `det_residueGram`, `dualCoefficientMatrix`, `residueGram_mul_dualCoefficientMatrix`, `residueGram_inv_eq_dualCoefficientMatrix` in [PolynomialResidueGram.lean](../Surreal/Algebra/PolynomialResidueGram.lean) | Reversing columns gives a lower triangular matrix with diagonal one, so its determinant is exactly `(-1)^(n(n-1)/2)`. The matrix with entries `P.coeff(i+j+1)` is proved to be the inverse Gram matrix through the explicit residue-dual basis. These statements hold over any commutative ring, at repeated roots and in degree zero. The bivariate divided-difference identity is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Bézout-kernel clause of `polynomial:thm:residuepairing`, `polynomial:eq:bezoutkernel` | `Surreal.FinitePolynomial.bezoutKernel`, `coeff_bezoutKernel`, `coeff_coeff_bezoutKernel`, `sub_mul_bezoutKernel`, `bezoutKernel_coefficientMatrix`, `residueGram_inv_eq_bezoutKernel_coefficientMatrix` in [PolynomialBezoutKernel.lean](../Surreal/Algebra/PolynomialBezoutKernel.lean) | The finite bivariate polynomial has exactly the explicit dual polynomials as coefficient columns and satisfies `(z-Y)Δ = P(z)-P(Y)` over every commutative ring. This realizes the polynomial difference quotient without dividing by a nonunit. Its finite coefficient matrix is the inverse residue Gram matrix for monic `P`. The polynomial identity itself needs no monicity, and degree-zero/zero-ring cases are included. The separate Laurent-coefficient identity at infinity is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Matrix factorization clause of `polynomial:eq:tracegram` | `Surreal.FinitePolynomial.residueGram_eq_pairing`, `quotient_traceMatrix_eq_residueGram_mul`, `quotient_det_traceMatrix_eq_sign_mul_norm` in [PolynomialTraceGram.lean](../Surreal/Algebra/PolynomialTraceGram.lean) | Mathlib's native trace matrix in the quotient power basis equals the residue Gram matrix times the multiplication matrix of the derivative. Its determinant is the fixed residue sign times the native quotient norm of the derivative. All coefficient rings are commutative; no separability or nonvanishing determinant assumption is needed. The universal identification with the native polynomial discriminant is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Determinant/resultant and discriminant clauses of `polynomial:thm:trace`, `polynomial:eq:tracegram` | `Surreal.FinitePolynomial.quotient_norm_eq_resultant`, `monic_resultant_derivative_eq_sign_mul_discr`, `quotient_det_traceMatrix_eq_discr` in [PolynomialNormResultant.lean](../Surreal/Algebra/PolynomialNormResultant.lean) | The determinant of multiplication by `Q` on the actual monic quotient is the native resultant `Res(P,Q)` over every commutative ring. Together with residue duality this identifies the native trace Gram determinant with the native polynomial discriminant. Mathlib's universal-coefficient induction descends degree-preserving remainder matrices from a splitting field; it does not assume the quotient is reduced or separable. Monicity removes derivative-degree padding, including degree drops in positive characteristic. Degree-zero and zero-ring cases are included. Combined with the trace and Gram rows above, this proves every assertion of the universal-ring trace theorem. **Proved**; build and axiom audit pass. |
| `polynomial:eq:lambdaatinfinity` in the residue-duality proof | `Surreal.FinitePolynomial.polynomialAtInfinity`, `reciprocalAtInfinity`, `polynomialAtInfinity_mul_reciprocal`, `quotientAtInfinity`, `polynomialAtInfinity_mul_quotient`, `quotientAtInfinity_eq_remainder_add_polynomial`, `coeff_quotientAtInfinity_eq_remainder`, `residueFunctional_eq_coeff_quotientAtInfinity` in [PolynomialResidueInfinity.lean](../Surreal/Algebra/PolynomialResidueInfinity.lean) | In Mathlib's actual Laurent series over any commutative ring, the variable is `T=z⁻¹`. Monicity supplies a unit-constant reciprocal of the reversed polynomial, and multiplication verifies the Laurent inverse and quotient. The coefficient of `T¹` in `Q/P` is exactly the top monic remainder coefficient. Polynomial parts have no positive Laurent exponents; degree-zero monic inputs and the zero ring are included. No field, ordinary analytic convergence or root-separation denominator is required. **Proved**; build and axiom audit pass. |
| Simple-root clause of `polynomial:thm:crt`, `polynomial:eq:lagrange` | `Surreal.FinitePolynomial.lagrange_formula`, `nodal_derivative_eval`, `nodal_derivative_eval_ne_zero`, `eval_lagrange_formula`, `lagrange_denominator_ne_zero` in [PolynomialLagrange.lean](../Surreal/Algebra/PolynomialLagrange.lean) | The displayed Lagrange polynomial identity reuses Mathlib's nodal polynomial and exact division by its selected linear factor. The scalar rational formula is proved away from the nodes, with every denominator nonzero. Valid over any field, without a lower bound on node separation; the degree hypothesis also handles an empty node set. Surcomplex specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Viète coefficient identity preceding `polynomial:eq:newton1`; `polynomial:eq:newton1`, `polynomial:eq:newton2` | `Surreal.FinitePolynomial.rootPowerSum`, `vieta_prod_coefficient`, `vieta_coefficient`, `newton_multiset_uniform`, `newton_identity_le_degree`, `newton_identity_gt_degree` in [PolynomialNewton.lean](../Surreal/Algebra/PolynomialNewton.lean) | The coefficient and both Newton identities are proved for monic split polynomials with roots counted as a multiset. The first regime requires `0 < k ≤ n`; the second includes degree-zero polynomials. Generic finite multiset identities hold over every commutative ring, and the field specializations impose no characteristic-zero assumption. Uses Mathlib's universal symmetric-polynomial identities with finite evaluation. Surcomplex specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:resultantproduct` and surrounding determinant, specialization, interchange-sign and common-root assertions | `Surreal.FinitePolynomial.resultant_eq_leadingCoeff_mul_prod_eval`, `resultant_eq_leadingCoeffs_mul_prod_sub`, `resultant_swap`, `resultant_eq_sylvester_det`, `sylvester_eq_matrix_bezout`, `resultant_map_fixed_degrees`, `resultant_map_of_injective`, `resultant_eq_zero_iff_common_root`, `sylvester_has_kernel_iff_common_root`, `resultant_ne_zero_iff_isCoprime` in [PolynomialResultant.lean](../Surreal/Algebra/PolynomialResultant.lean) | Mathlib's resultant at the actual degrees has the root products with both leading-coefficient powers and the Sylvester determinant interpretation. Arbitrary coefficient maps preserve a fixed-size determinant; injectivity additionally preserves actual degrees. The common-root criterion assumes the first polynomial is nonzero and split, and permits a zero second polynomial. The finite Bézout map is identified with the Sylvester matrix in explicit bases, and a nonzero kernel vector characterizes common roots. Coprimality requires no splitting. Native `Res(0,0)=1` is documented. Discriminants and Hahn valuation identities are mapped separately below. Quotient multiplication determinants are mapped separately with the universal trace theorem; surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:discdef` and its repeated-root assertion | `Surreal.FinitePolynomial.leadingCoeff_mul_discr_eq_sign_mul_resultant`, `discr_eq_sign_mul_resultant`, `discr_ne_zero_iff_squarefree`, `discr_eq_zero_iff_repeated_root`, `discr_C_mul_prod_X_sub_C`, `discr_prod_X_sub_C`, `discr_eq_leadingCoeff_pow_mul_prod_sub_sq` in [PolynomialDiscriminant.lean](../Surreal/Algebra/PolynomialDiscriminant.lean) | Uses Mathlib's native discriminant and actual-degree resultant in characteristic zero. The squared root-difference formula includes the leading-coefficient power and counts repeated root occurrences. Positive degree guards the general formula; monic constants and native discriminant-one conventions are included. The squarefree criterion needs no splitting, while the repeated-root criterion assumes a nonzero split polynomial. Valuation and quotient trace-pairing identities are mapped separately; surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:prop:rootbounds`, `polynomial:eq:cauchybound` | `Surreal.FinitePolynomial.root_lt_cauchy_bound`, `reciprocal_cauchy_bound_lt_root`, `root_le_two_mul_radialCoefficientMax`, `root_eq_zero_of_radialCoefficientMax_eq_zero`; `Surreal.Complexify.modulus_root_lt_cauchy_bound`, `reciprocal_cauchy_bound_lt_modulus_root`, `modulus_root_le_two_mul_radialCoefficientMax` in [PolynomialRootBounds.lean](../Surreal/Algebra/PolynomialRootBounds.lean) | Both strict Cauchy bounds use the exact finite maxima in the source, with a nonzero constant coefficient for the lower bound. The radial maximum uses nonnegative `(n-j)`th roots in a real closed ordered base field and proves the non-strict bound `2M`, including the zero-maximum conclusion. The abstract proofs use an ordered-field-valued absolute value, specialized to the existing base-field modulus of `Complexify F`; no Archimedean assumption or real-valued norm is introduced. Positive degree makes all maxima nonempty. The strict Cauchy bounds and certified-radius bound are instantiated on concrete surcomplex numbers below; the exact arbitrary-root radial maximum remains pending there. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:thm:gausslucas`, `polynomial:eq:barycentric` | `Surreal.FinitePolynomial.critical_point_eq_barycentric_grouped`, `groupedCriticalRootWeight_pos`, `normalizedCriticalRootWeight_pos`, `sum_normalizedCriticalRootWeight`, `sum_normalizedCriticalRootWeight_smul`, `critical_point_mem_convexHull_roots`, `iterate_derivative_roots_subset_convexHull` in [PolynomialGaussLucas.lean](../Surreal/Algebra/PolynomialGaussLucas.lean) | The exact barycentric identity is proved both by root occurrences and with grouped algebraic multiplicities. Nonroot critical points have strictly positive base-field-valued weights with sum one. The native convex hull uses the ordered field `F` with nonnegative square roots, including non-Archimedean fields, and also contains critical points which are roots. The first-derivative theorem assumes splitting and positive degree; higher derivatives assume splitting of each preceding derivative and nonvanishing of the final derivative. The concrete surcomplex specialization under these same splitting hypotheses is proved below; unconditional splitting and algebraic closedness remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Concrete Cauchy clauses of `polynomial:prop:rootbounds` / `polynomial:eq:cauchybound`; split-case `polynomial:thm:gausslucas` and `polynomial:eq:barycentric` | `Surreal.Surcomplex.modulusAbsoluteValue`, `root_lt_cauchy_bound`, `reciprocal_cauchy_bound_lt_root`, `root_le_two_mul_of_coeff_le_pow`, `critical_point_eq_barycentric_grouped`, `critical_point_mem_convexHull_roots`, `iterate_derivative_roots_subset_convexHull` in [Surcomplex/PolynomialGeometry.lean](../Surreal/Surcomplex/PolynomialGeometry.lean) | Both strict source Cauchy bounds hold for roots of actual surcomplex polynomials with positive degree, retaining the nonzero constant-coefficient guard for the lower bound. An explicit coefficient-domination certificate gives the radial bound without requiring arbitrary-degree roots. Gauss–Lucas and the exact grouped barycentric formula hold on the concrete carrier under explicit splitting; nonroot critical points are required for the displayed weights. Higher derivatives retain splitting of every preceding derivative and nonvanishing of the final one. The modulus and convex coefficients are surreal-valued. **Proved** for the Cauchy and certified-radius clauses; **prerequisites proved** for the full Gauss–Lucas statement. Algebraic closedness/unconditional splitting and the source radial maximum involving arbitrary-degree roots remain pending. Build and axiom audit pass. |
| `polynomial:eq:resval` and the nodal derivative separation sum defining `dᵢ` | `Surreal.HahnSeries.orderTop_resultant_eq_sum_eval`, `orderTop_resultant`, `order_resultant`, `orderTop_nodal_derivative_eval`, `order_nodal_derivative_eval` in [PolynomialValuation.lean](../Surreal/HahnSeries/PolynomialValuation.lean) | Resultant valuations retain the leading-coefficient powers and every root-pair occurrence. The formulas with `orderTop` retain infinity when products vanish; exponent-group-valued `order` formulas require nonzero polynomials/resultant or injective nodes. Splitting is explicit, and no Hahn algebraic closedness or surreal embedding is assumed. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:discval` | `Surreal.HahnSeries.orderTop_discr_eq_pair_sum`, `order_discr_eq_pair_sum`, `orderTop_discr_eq_sum_derivative`, `order_discr_eq_sum_derivative` in [DiscriminantValuation.lean](../Surreal/HahnSeries/DiscriminantValuation.lean) | Over a characteristic-zero Hahn coefficient field, the discriminant valuation is the leading-coefficient term plus twice the pairwise separation sum. The positive-degree formula uses an explicit indexed factorization; injective roots give the exponent-group-valued version. For monic split polynomials, it is also the sum of derivative valuations at root occurrences, including the degree-zero empty sum. The `orderTop` versions permit vanishing discriminants; the finite monic version requires a nonzero discriminant. Hahn algebraic closedness and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:weighted`, `polynomial:eq:active`, `polynomial:lem:gaussvaluation` and following normalization assertions | `Surreal.HahnSeries.gaussExpansion`, `coeff_coeff_gaussExpansion`, `gaussExpansion_injective`, `weightedGaussVal`, `weightedGaussVal_eq_inf`, `weightedGaussVal_mul`, `weightedGaussVal_add`, `gaussInitial_ne_zero`, `gaussInitial_mul`, `orderTop_normalizedGaussCoefficient_nonneg`, `coeff_gaussInitial_eq_standardPart`, `exists_normalizedGaussCoefficient_orderTop_eq_zero`, `coeff_gaussInitial_ne_zero_iff`, `support_gaussInitial_eq_active`, `gaussInitial_active_extrema` in [PolynomialGaussValuation.lean](../Surreal/HahnSeries/PolynomialGaussValuation.lean) | Regrouping a finite polynomial into Hahn series with polynomial coefficients defines a faithful expansion at any center and any weight in the ordered exponent group. Its native Hahn valuation is exactly the finite minimum of weighted Taylor-coefficient valuations; infinity occurs precisely at the zero polynomial. Leading coefficients give nonzero multiplicative initial polynomials, and the actual standard-part map extracts their normalized coefficients. Every normalized coefficient has nonnegative order and at least one has order zero for nonzero input. No Archimedean, divisibility, characteristic-zero or algebraic-closedness assumption is imposed. The initial support consists exactly of the active indices, and its trailing degree and degree are their least and greatest elements. Root counts for explicitly split polynomials are mapped below; the surreal bridge remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:thm:initialroots`, `polynomial:eq:initialroots`, `polynomial:eq:profileproduct`, `polynomial:eq:closedcount`, `polynomial:eq:opencount`, `polynomial:eq:shellcount` | `Surreal.HahnSeries.weightedGaussVal_X_sub_C`, `weightedGaussVal_split`, `gaussInitial_split_standardPart`, `initialRootScalar_ne_zero`, `natDegree_gaussInitial_split`, `natTrailingDegree_gaussInitial_split`, `shell_count_gaussInitial_split`, `rootMultiplicity_gaussInitial_split_direction` in [PolynomialInitialRoots.lean](../Surreal/HahnSeries/PolynomialInitialRoots.lean) | For an explicit finite factorization, the weighted profile is the leading-scalar valuation plus the sum of root-separation minima. The initial polynomial has the exact standard-part factors for closed-ball roots and an explicit nonzero scalar from outside roots. Its degree, trailing degree and their difference count closed/open/shell roots with multiplicities; the multiplicity of each residue counts the corresponding residue-direction ball. Repeated roots, coincident residues, empty products and roots at the center with valuation infinity are retained. Counting assumes a nonzero leading scalar. Combined with active-index extrema above this gives the source's `j₋` and `j₊` counts. No algebraic closedness, characteristic-zero, divisible-group or rank-one assumption is introduced. The concrete surreal bridge remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:cor:valrouche`, `polynomial:eq:valrouche` | `Surreal.HahnSeries.weightedGaussVal_add_eq_of_lt`, `gaussInitial_add_eq_of_lt`, `valuationRouche`, `valuationRouche_closed_count`, `valuationRouche_open_count`, `valuationRouche_shell_count`, `valuationRouche_direction_count` in [PolynomialRouche.lean](../Surreal/HahnSeries/PolynomialRouche.lean) | A perturbation of strictly higher weighted valuation preserves the exact profile value and entire initial polynomial, including its scalar. Zero error is included by valuation infinity; the strict hypothesis already forces the original polynomial to be nonzero. Root-count consequences use independent nonzero finite split factorizations of the two polynomials, allowing different degrees and root index types while preserving multiplicities. No contour, topology, algebraic-closedness, characteristic or rank assumption is introduced. Concrete surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:thm:newton`, actual breakpoint finiteness and leading-coefficient multiplicities | `Surreal.HahnSeries.newtonActiveIndices`, `newtonSpan`, `rootValuationCount_eq_newtonSpan`, `rootValuationCount_eq_of_active_extrema`, `newtonBreakpoint_iff_exists_root`, `isRoot_newtonBreakpoint_order`, `infinite_valuation_root_count`, `rootMultiplicity_initial_eq_leadingCoeff_count`, `mem_newtonBreakpointValues`, `finite_newtonBreakpoints` in [PolynomialNewtonProfile.lean](../Surreal/HahnSeries/PolynomialNewtonProfile.lean) | At center zero, the largest minus smallest active index counts the multiset of roots at the chosen finite valuation. At least two active indices occur exactly at the valuations of nonzero roots. Nonzero initial-root multiplicities count original roots with that valuation and leading coefficient; zero roots are counted separately at infinity. The finite set of nonzero-root orders is exactly the breakpoint set. The polynomial is nonzero and explicitly split; arbitrary ordered exponent groups are allowed. Constructing candidate breakpoints by rational coefficient slopes, affine-region slope analysis and the surreal interpretation remain separate obligations. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:lem:initialderivative`, `polynomial:eq:initialderivative` | `Surreal.HahnSeries.gaussExpansion_derivative`, `centeredGaussExpansion_derivative`, `normalizedGaussExpansion_derivative`, `weightedGaussVal_derivative`, `gaussInitial_derivative`, `initialDerivative`, `initialIterateDerivative` in [PolynomialInitialDerivative.lean](../Surreal/HahnSeries/PolynomialInitialDerivative.lean) | The exact formal chain rule shifts Hahn exponents by the scale. If the leading initial polynomial has nonzero derivative, differentiation lowers the weighted value by the scale and gives exactly its ordinary derivative as the new initial polynomial. In residue characteristic zero, positive initial degree suffices; all iterates through that degree have value `w(P)-rρ` and initial polynomial `I(P)^(r)`. The zeroth iterate is included and finite shifts use `WithTop` without assigning a finite order to zero. No constant-initial or positive-characteristic nonvanishing claim is assumed. Concrete surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:thm:criticalballs`; all-root-ball containment clause of `polynomial:cor:nearest` | `Surreal.HahnSeries.closedBallRootCount`, `openBallRootCount`, `closedBallRootCount_iterate_derivative`, `openBallRootCount_iterate_derivative`, `directionRootCount_iterate_derivative`, `critical_direction_count`, `criticalPoint_mem_closedBall`, `criticalPoint_mem_openBall` in [PolynomialCriticalBalls.lean](../Surreal/HahnSeries/PolynomialCriticalBalls.lean) | Native root multisets count multiplicities in closed/open valuation balls. If the original count is `k`, the `r`th derivative has count `k-r` for `r≤k`, with occupation forced whenever `r>0`; the zeroth case is included. The relevant derivative is proved nonzero even at `r=k`. Its residue-direction multiplicities are those of the corresponding initial derivative. Every closed or open ball containing all roots also contains all critical points. Residue characteristic zero and splitting of the original and relevant derivative are explicit. The nearest-neighbour maximum equality is proved below; Hahn algebraic closedness and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Nearest-neighbour clause of `polynomial:cor:nearest`; `polynomial:eq:nearest` | `Surreal.HahnSeries.criticalPoint_orderTop_le_of_otherRoots_le`, `exists_criticalPoint_orderTop_eq_of_nearest_root`, `otherRootValues`, `criticalPointValues`, `nearestCriticalValue` in [PolynomialNearestCritical.lean](../Surreal/HahnSeries/PolynomialNearestCritical.lean) | For a squarefree polynomial of degree at least two, the finite valuations of displacements from a chosen root to other roots and to critical points have a common attained greatest element. No critical point equals the chosen root. Open-ball count one excludes every closer critical point; closed-ball count at least two supplies a critical point on the nearest-root shell. Both the polynomial and its derivative explicitly split, and residue characteristic zero is retained. Valuations of zero are excluded before finite-order comparisons. Hahn algebraic closedness and concrete surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `trigonometry:eq:dotcross`, `trigonometry:eq:gram` and following triangle-equality characterization | `Surreal.Complexify.dot`, `cross`, `dot_sq_add_cross_sq`, `abs_dot_le`, `modulus_add_eq_iff_dot`, `modulus_add_eq_iff_pos_quotient` in [Geometry.lean](../Surreal/Algebra/Geometry.lean) | Coordinate identities and the equality criterion for nonzero vectors over any ordered field with nonnegative square roots. The positive quotient is an embedded element of that same base field. The concrete surcomplex equality criterion is proved below. **Prerequisites proved**; build and axiom audit pass. |
| Area clause of `trigonometry:thm:heron`, factorization behind `trigonometry:eq:heronfactor` | `Surreal.Complexify.heron_factorization`, `heron`, `triangleArea` | Heron's identity for the triangle with vertices `0,z,w`, including degenerate cases, over an ordered field with nonnegative square roots. The concrete surcomplex specialization is proved below; radius, incenter, bisector and half-angle clauses remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Inequality clause of `trigonometry:thm:ptolemy` | `Surreal.Complexify.ptolemy_identity`, `ptolemy` | The four-point inequality over any real closed ordered base field. Cyclic order and the cyclic equality case remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Finite normalization for the Hahn closedness assertions in `found:sub:hahncomplex`, `polynomial:prop:workspace` | `Surreal.FinitePolynomial.scalePolynomial`, degree, coefficient, reconstruction and affine root-pullback formulas in [PolynomialScaling.lean](../Surreal/Algebra/PolynomialScaling.lean); `exists_coprime_monic_factors`, `exists_odd_coprime_monic_factors_of_root`, `realClosed_depressed_odd_coprime_factorization` in [RealClosedPolynomialFactors.lean](../Surreal/Algebra/RealClosedPolynomialFactors.lean); `Surreal.HahnSeries.exists_weighted_monomial_normalization`, `exists_monic_reduction`, `exists_monic_depressed_reduction` in [PolynomialNormalization.lean](../Surreal/HahnSeries/PolynomialNormalization.lean) | Generic field scaling preserves monicity and degree and supplies exact root pullbacks; the actual sign-field API now reuses it. In a divisible ordered abelian exponent group, an attained minimum of the finitely many weighted orders makes every coefficient nonnegative in valuation and retains a nonzero lower residue. The resulting monic residue has the same degree, retains the depressed coefficient, and is not a pure power. The exponent group needs no field structure or Archimedean hypothesis. Finite coprime factor extraction uses only an existing residue root; ordinary real-closed coefficients supply odd roots. **Proved** prerequisites for the full fixed-Hahn closedness constructions below. Build and axiom audit pass. |
| Global square roots in the real Hahn workspace of `found:sub:hahncomplex` | `Surreal.HahnSeries.leadingNormalized`, `orderTop_leadingNormalized_sub_one_pos`, `leadingMonomial_mul_leadingNormalized`, `exists_pos_square_root_of_coefficients`, `existsUnique_nonneg_square_root`, `hahnLexHasNonnegSquareRoots`, `isSquare_of_nonneg_lex` in [SquareRoots.lean](../Surreal/HahnSeries/SquareRoots.lean) | Every nonnegative lexicographic Hahn series has a unique nonnegative square root when the coefficient field has nonnegative square roots and the exponent group is divisible. Leading-term normalization gives one plus a positive-order error; the already constructed binomial half-power, a coefficient square root and a halved exponent give the exact root. Zero and pure monomials are included. This uses the weaker square-root interface and assumes no Hahn real closedness. **Proved** on the fixed Hahn carrier. Build and axiom audit pass. |
| Real and algebraic closedness clauses in `found:sub:hahncomplex`, `found:sub:localization`, `polynomial:prop:workspace` | `Surreal.HahnSeries.hahnCharZero` in [Characteristic.lean](../Surreal/HahnSeries/Characteristic.lean); `exists_root_of_monic_of_isAlgClosed`, `exists_root_of_isAlgClosed_coefficients`, `hahnIsAlgClosed` in [AlgebraicallyClosed.lean](../Surreal/HahnSeries/AlgebraicallyClosed.lean); `exists_isRoot_of_monic_odd_natDegree`, `exists_isRoot_of_odd_natDegree`, `exists_isRoot_of_odd_natDegree_lex`, `hahnLexIsRealClosed`, `hahnIsRealClosed` in [RealClosed.lean](../Surreal/HahnSeries/RealClosed.lean) | Over a divisible ordered abelian exponent group, Hahn fields with algebraically closed characteristic-zero coefficients are algebraically closed, and Hahn fields with ordered real-closed coefficients are real closed. The proofs translate and scale each polynomial, extract proper coprime residue factors, lift them using the constructed Hahn Hensel theorem, and induct on strictly smaller degree. Pure powers give explicit roots; monic normalization handles all nonconstant inputs. The real proof selects a proper odd-degree factor and combines odd roots with the constructed square roots. Characteristic zero transfers through the injective constant map. These are proved native `IsAlgClosed` and `IsRealClosed` instances, with no closure hypothesis on the Hahn field. [RealClosedReal.lean](../Surreal/Algebra/RealClosedReal.lean) supplies the ordinary real coefficient instance missing from the pinned Mathlib, using its square roots and intermediate value theorem; the default audit explicitly checks both ordinary real and complex Hahn instantiations. **Proved** for the fixed-Hahn closedness assertions; embedding arbitrary actual surreal data and constructing the normal-form bridge remain pending. Build and axiom audit pass. |
| Fixed complex-Hahn factorization in `polynomial:thm:fta`, `polynomial:eq:factorization`; root persistence in `found:thm:workspace`, `polynomial:prop:workspace`; finite-point image containment in `found:thm:finitepoints` | `Surreal.HahnSeries.complex_polynomial_splits`, `complex_polynomial_exists_root`, `complex_polynomial_factorization`, `complex_polynomial_roots_card`, `complex_polynomial_exists_unique_factorization`, `complex_polynomial_roots_map`, `complex_polynomial_root_mem_range`, `complex_finite_algebra_character_descends` in [PolynomialWorkspace.lean](../Surreal/HahnSeries/PolynomialWorkspace.lean) | Instantiates the existing finite algebra in the constructed complex Hahn field: all polynomials split in their original divisible workspace; nonconstant polynomials have roots; the scalar/multiset factorization is unique for nonzero inputs and has the exact degree count. Every extension preserves root locations and multiplicities. A character of a finite workspace algebra takes values in the original workspace even in a larger field. No additional splitting or closedness premise is assumed. **Proved** for these fixed-Hahn clauses; local algebra lengths, containment of actual surcomplex input data and the surreal interpretation remain separate obligations. Build and axiom audit pass. |
| Root-persistence clause of `found:thm:workspace` | `Surreal.FinitePolynomial.roots_map`, `root_mem_range`, `roots_map_of_isAlgClosed` | Roots and multiplicities of split polynomials under field extension. Workspace construction, support compatibility and the other localization clauses remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Coefficientwise complexification in the proof of `polynomial:prop:workspace` | `Surreal.HahnSeries.complexifyHahnEquiv`, `coeff_complexifyToHahn`, `coeff_hahnToComplexify_re`, `coeff_hahnToComplexify_im`, `support_complexifyToHahn` in [HahnSeries/Complexify.lean](../Surreal/HahnSeries/Complexify.lean) | A ring equivalence between the quadratic extension of Hahn series over `R` and Hahn series with coefficients in `R[i]`, for any commutative ring `R`. Real and imaginary projection supports are contained in the original support, and the combined support is exactly their union. Native coefficient and conjugation results are mapped below. Closure and surreal workspace construction remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `K_Γ = F_Γ[i]` and conjugation-fixed-field identification in `polynomial:prop:workspace` | `Surreal.Complexify.complexEquiv` in [Algebra/ComplexNumbers.lean](../Surreal/Algebra/ComplexNumbers.lean); `Surreal.HahnSeries.conjugation_eq_self_iff_mem_range` in [Conjugation.lean](../Surreal/HahnSeries/Conjugation.lean); `realComplexHahnEquiv`, `complexConjugation_realComplexHahnEquiv`, `complexConjugation_eq_self_iff_mem_range`, `orderTop_complexConjugation`, `realHahnSubfieldEquiv`, `mem_realHahnSubfield_iff` in [HahnSeries/ComplexNumbers.lean](../Surreal/HahnSeries/ComplexNumbers.lean) | The quadratic algebra over native `ℝ` is ring-isomorphic to native `ℂ`, compatibly with scalar inclusion, `i`, and conjugation. Thus complex Hahn series are the quadratic extension of real Hahn series; the conjugation-fixed elements are precisely the injectively embedded real Hahn series. Conjugation preserves support and Hahn order. The generic fixed-image theorem assumes a characteristic-zero coefficient field; the ring statements allow ordered cancellative exponent monoids. For exponent groups, the real image is a bundled subfield, isomorphic to the real Hahn field and characterized by conjugation fixedness. Real/algebraic closedness of these Hahn fields is now constructed above for divisible exponents. The actual surreal embedding remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Image-containment clause of `found:thm:finitepoints` | `Surreal.FinitePolynomial.finite_algebra_character_descends` | A character of a finite algebra over an algebraically closed base takes values in that base. Local decomposition and base-change/local-length assertions remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `a:lem:neumann`, `a:rule:wordlength` | `Surreal.HahnSeries.neumann_add`, `finite_words_of_sum_eq`, `finite_nondecreasing_words_of_sum_eq`, `neumann_positive` in [Neumann.lean](../Surreal/HahnSeries/Neumann.lean) | **Proved** over an arbitrary ordered abelian group: well-ordered sumsets, finite pair-sum fibers, a well-ordered positive generated monoid, and finite fixed-sum word fibers across all lengths. The all-word version strengthens the requested nondecreasing-word statement. Uses Mathlib's partial well-order and Higman APIs. |
| Full finite-word support lemma `dyn:lem:neumann`; corrected combinatorial depth in `dyn:cor:ancestry` | `Surreal.HahnSeries.isPWO_add_positive_closure`, `finite_shifted_words_of_sum_eq`, `exists_shifted_word_length_bound`, `exists_shifted_nonempty_word_depth_bound`, finite contributing inputs/letters, `positiveMonomialShift`, `iterate_positiveMonomialShift_negative_monomial`, `no_input_independent_ancestry_depth` in [Ancestry.lean](../Surreal/HahnSeries/Ancestry.lean), together with [Neumann.lean](../Surreal/HahnSeries/Neumann.lean) | An arbitrary well-ordered input support plus the positive generated monoid is well ordered. At each output exponent, only finitely many input-exponent/word pairs contribute, so a finite depth bound exists depending on that input support. The earlier full word lemma supplies the unshifted part. The actual complex-linear shift on complex Hahn series proves `T^n(t^(-n)) = 1` and excludes every input-independent bound at output zero, checking the documented correction below. **Proved** for the support lemma, corrected combinatorial bounds and counterexample. The full operator-summability assertion remains pending. Build and axiom audit pass. |
| Constant-family specialization of `a:def:summable`, `a:rule:clauseii`; nonsummability part of `a:ex:notsummable` | `Surreal.HahnSeries.summable_constants_iff`, `hsum_constants`, `not_summable_constants_of_infinite`, `not_summable_geometric_constants` in [Constants.lean](../Surreal/HahnSeries/Constants.lean) | A family of constants is strongly summable exactly when its coefficient function has finite support. The nonzero constants `2⁻ⁿ` give a counterexample even though their support union is contained in `{0}`. Uses Mathlib's actual `SummableFamily`; ordinary analytic convergence and surreal interpretation are separate obligations. **Prerequisites proved**; build and axiom audit pass. |
| Regrouping and interchange assertions following `a:def:summable` | `Surreal.HahnSeries.restrict`, `regroup`, `coeff_hsum_fiber`, `coeff_regroup`, `hsum_regroup`, `hsum_fubini` in [Regroup.lean](../Surreal/HahnSeries/Regroup.lean) | Any index map regroups a jointly summable Hahn family into a summable family of fiber sums with unchanged total. Includes infinite fibers and double-sum interchange, with joint summability explicit throughout. Uses finite coefficient families rather than a topological convergence operation. The surreal interpretation remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Algebraic standard-part claims in `a:eq:st` and the following decomposition | `Surreal.HahnSeries.nonnegativeSubring`, `standardPart`, `standardPart_surjective`, `mem_infinitesimalIdeal`, `infinitesimalIdeal_isMaximal`, `residueEquiv`, `exists_unique_standardPart_decomposition` in [StandardPart.lean](../Surreal/HahnSeries/StandardPart.lean) | On the nonnegative-order Hahn subring over a coefficient field, coefficient-zero extraction is a surjective ring homomorphism with maximal positive-order kernel. The quotient is the coefficient field, and the constant-plus-positive-order decomposition is unique. Zero has order infinity and is included. The ordinary modulus-bounded surcomplex ring and its standard part are constructed above; identification of this Hahn coefficient map with that actual standard part remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:reductionfactor` and its preceding root/coefficient assertions | `Surreal.HahnSeries.orderTop_nonneg_of_monic_root`, `orderTop_nonneg_of_monic_root_of_coeff_nonneg`, `coeff_orderTop_nonneg_of_monic_split_roots`, `coeff_orderTop_nonneg_multiset_prod`, `splits_nonnegative_of_splits`, `standardPart_factorization`, `roots_standardPart` in [PolynomialReduction.lean](../Surreal/HahnSeries/PolynomialReduction.lean) | Roots of monic polynomials with nonnegative-order coefficients have nonnegative order. The converse holds for split monic polynomials, including finite products. A monic polynomial over the nonnegative-order subring that splits in the Hahn field already splits in the subring. Standard part preserves the complete linear factorization and maps the root multiset, adding multiplicities when reductions coincide. Splitting is explicit in this general theorem; the proved closedness instance now supplies it over complex coefficients and divisible exponents. Identification with surreal modulus-boundedness remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Actual surcomplex root and reduction assertions in `polynomial:eq:reductionfactor` | `Surreal.Surcomplex.finiteSubring_integers`, `finite_of_integral`, `finite_of_monic_root`, `finite_of_monic_root_of_coeff_finite`, `coeff_finite_of_monic_split_roots`, `coeff_finite_multiset_prod`, `splits_finite_of_splits`, `standardPart_factorization`, `roots_standardPart`, `isRoot_standardPart` in [Surcomplex/PolynomialReduction.lean](../Surreal/Surcomplex/PolynomialReduction.lean) | Mathlib’s integrality theorem for valuation rings proves that every actual surcomplex root of a monic polynomial with finite coefficients is finite. Conversely, finite roots of a split monic polynomial give finite coefficients. Splitting in the actual ambient field descends to its finite ring, and the ordinary-complex standard-part map preserves the full linear factorization and root multiset, adding multiplicities at coincident reductions. Every finite root reduces to a root. **Proved** with the explicit splitting hypotheses shown; the source’s unconditional splitting still depends on pending surcomplex algebraic closedness. Build and axiom audit pass. |
| Uniqueness and coprimeness clauses of `polynomial:thm:hensel` | `Surreal.FinitePolynomial.isCoprime_of_monic_reductions`, `monic_factorization_unique_of_reductions`, `monic_finite_factorization_unique_of_reductions` in [Algebra/PolynomialFactorUniqueness.lean](../Surreal/Algebra/PolynomialFactorUniqueness.lean); native standard-part specializations in [HahnSeries/PolynomialFactorUniqueness.lean](../Surreal/HahnSeries/PolynomialFactorUniqueness.lean) and [Surcomplex/PolynomialFactorUniqueness.lean](../Surreal/Surcomplex/PolynomialFactorUniqueness.lean) | Unit reflection of the residue homomorphism and monic preservation of resultant degrees lift coprimeness. Cross-coprimeness, divisibility and preserved degrees prove uniqueness of every finite monic factor family with the same pairwise coprime reductions, including empty families and constant factors. The hypothesis that the standard-part map reflects units is proved for both the nonnegative Hahn ring and the actual finite surcomplex ring. Candidates need no preassigned support monoid or formal-series presentation. **Proved** for these uniqueness and coprimeness clauses; factor existence and its support certificate remain separate. Build and axiom audit pass. |
| Univariate summability and ring-compatibility clauses of `a:cor:complexsub` | `Surreal.HahnSeries.evaluate`, `evaluate_X`, `summable_coeff_mul_powers`, `coeff_evaluate`, `coeff_zero_evaluate`, `summable_powers` in [Evaluation.lean](../Surreal/HahnSeries/Evaluation.lean) | Admissible evaluation reuses Mathlib `PowerSeries.heval` as an algebra homomorphism, with an explicit positive-`orderTop` proof and the actual coefficient-times-power term formula. Zero is included because its `orderTop` is infinity. Univariate composition is mapped separately below. Finite-variable evaluation is mapped below; differentiation and the surreal bridge remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Finite-variable summability and algebra-homomorphism clauses of `a:cor:complexsub`; support control for `polynomial:thm:hensel` | `Surreal.HahnSeries.summable_finite_products`, `mvPowerFamily`, `mvEvaluationFamily`, `summable_mv_coeff_mul_powers`, `finite_mv_coeff_support`, `isPWO_mv_support`, `mvEvaluate`, `coeff_mvEvaluate`, `coeff_zero_mvEvaluate`, order bounds, `support_mvEvaluate_subset_closure` in [MvEvaluation.lean](../Surreal/HahnSeries/MvEvaluation.lean) | Every formal power series in finitely many variables evaluates at positive-order Hahn inputs through an actual algebra homomorphism. Finite products of summable power families prove joint summability; regrouping the product by multiindex addition proves multiplication. Each Hahn coefficient receives finitely many contributions, and the support lies in the additive monoid generated by the input supports. Constant coefficients are preserved; all outputs have nonnegative order, and zero-constant inputs give positive order. Zero variables and arbitrary ordered cancellative exponent monoids are allowed; coefficient rings may have zero divisors. Finite-variable composition is mapped below; differentiation and the actual surreal bridge remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Univariate composition clause of `a:cor:complexsub` | `Surreal.HahnSeries.orderTop_evaluate_nonneg`, `orderTop_evaluate_pos_of_constantCoeff_zero`, `coeff_evaluate_eq_sum`, `evaluate_subst` in [Composition.lean](../Surreal/HahnSeries/Composition.lean) | Evaluation of arbitrary formal power series commutes with formal substitution when the inner series has zero constant coefficient and the Hahn argument has positive order. The evaluated inner series is itself proved admissible. Coefficientwise finite-support calculations justify the interchange, including zero inner series or argument. Finite-variable Hahn composition is now mapped below; analytic coefficient-ring interpretations and the surreal bridge remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Finite-variable composition clause of `a:cor:complexsub` | `Surreal.HahnSeries.summable_mv_composition_coefficients`, `coeff_mvEvaluate_eq_sum`, `mvEvaluate_subst` in [MvComposition.lean](../Surreal/HahnSeries/MvComposition.lean) | Strong Hahn evaluation commutes with native multivariate formal substitution when all inner series have zero constant term and the finitely many Hahn arguments have positive order. Evaluated inner values are proved to have positive order. A constructed jointly summable double family and explicit finite coefficient fibers justify interchange; arbitrary outer coefficients and rings with zero divisors are allowed. No fine-topological continuity or convergence is assumed. **Proved** for this formal Hahn composition clause; differentiation and the actual surreal interpretation remain pending. Build and axiom audit pass. |
| `a:eq:geom` and formal remainder in `a:ex:geometric` | `Surreal.HahnSeries.geometric_mul`, `geometric_hsum`, `geometric_remainder` | The strongly summable power family has sum `(1-x)⁻¹`, with exact finite-sum remainder `x^(N+1)/(1-x)`, when `x` has positive order. The identity is generic Hahn algebra. The valuation calculation at the named surreal scale and nonconvergence in the fine topology remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Binomial specialization of `a:cor:complexsub`; root identity used in `b:ramification` and local trigonometric binomial expansions | `Surreal.HahnSeries.binomialTerms_apply`, `binomialPower_eq_hsum`, `orderTop_binomialPower_sub_one_pos`, `binomialPower_add`, `binomialPower_nat`, `binomialPower_rat_root`, `binomialPower_half_sq` in [Binomial.lean](../Surreal/HahnSeries/Binomial.lean); `pow_injective_near_one`, `binomialPower_rat_root_unique`, `exists_unique_root_near_one` in [BinomialRoots.lean](../Surreal/HahnSeries/BinomialRoots.lean) | The proof-gated binomial family has the actual terms `choose r n • x^n`, constant coefficient one, positive-order difference from one, and formal exponent-addition/natural-power laws. Rational exponents give an `m`th root of `1+x` for nonzero natural `m`. Over a characteristic-zero Hahn field, this is the unique root whose difference from one has positive order, using the geometric factor's nonzero standard part `m`. The positive ordered-root identification is mapped below. Ramification normal forms, analytic convergence and the surreal interpretation remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Positive square-root branch in the local trigonometric binomial expansions | `Surreal.HahnSeries.lex_pos_of_sub_one_orderTop_pos`, `binomialPower_lex_pos`, `binomialPower_half_eq_of_nonneg_sq`, `exists_unique_nonneg_sqrt_one_add` in [BinomialOrder.lean](../Surreal/HahnSeries/BinomialOrder.lean) | Over any ordered coefficient field, every rational binomial power near one is positive in Mathlib's lexicographic Hahn order. The half-power is the unique nonnegative square root of `1+x` when `x` has positive order, including zero `x`. The constructed local root needs no real-closedness assumption. Global nonnegative Hahn square roots are now constructed above for divisible exponents. Analytic convergence and the surreal bridge remain pending. **Prerequisites proved**; build and axiom audit pass. |

## Dependency order

1. **Size guards and finite algebra (Layer A).** First prove the unrestricted
   bound/cut contradictions (`found:prop:allcuts`) for an irreflexive relation.
   Define complexification of a commutative ring with multiplication
   `(a,b)(c,d) = (ac-bd, ad+bc)`, its scalar embedding, `i`, conjugation and norm
   square. Prove coordinate identities, involution, norm multiplicativity and
   Gram's identity before introducing order. Ordered-field positivity then
   justifies inverses; real closedness is an additional prerequisite for square
   roots and algebraic closedness. Source anchors: `found:eq:pairmul`,
   `found:eq:conj`, `found:eq:pairinv`, `found:prop:complex`, `found:eq:gram`,
   `found:eq:rationalcircle`, `trigonometry:eq:dotcross`, and
   `trigonometry:eq:gram`. The full `found:prop:complex` also asserts real-closed
   and class-coded conclusions; coordinate algebra alone does not complete it.
2. **Ordered algebra and finite polynomial consequences.** Establish the rational
   unit-circle parametrization and reusable finite linear/polynomial algebra.
   Factorization needs algebraic closedness; norm geometry needs the appropriate
   ordered/real-closed input. Early polynomial targets include
   `polynomial:thm:fta` and `polynomial:thm:crt`, followed by the finite-algebra
   descent theorem `found:thm:finitepoints`. Keep generic proofs separate from
   their surreal specializations.
3. **Set-sized Hahn support and evaluation (Layer B).** Prove well-ordering and
   local finiteness for admissible support families, support-preserving sums,
   positive-support geometric/binomial series, and admissible substitution.
   Then define standard part and Taylor lifting with recentering. Initial
   anchors include `polynomial:lem:support`, `trigonometry:lem:support`,
   `found:prop:positive`, and `found:cor:fixeddomain`.
4. **Coefficient rings and coherent functions (Layer C).** Give separate types
   to the four coefficient-ring conventions in the document map. Establish
   coefficientwise differentiation/integration and support-controlled
   composition, then local division/preparation, finite deformations, and
   residue duality. The analytic-geometry ring table must be checked before
   transporting any theorem between these types. Follow with contours and
   Stokes, global divisors, and the remaining polynomial/trigonometric results.
5. **Universe-indexed surreal construction and bridge (Layer D, independent
   foundational track).** Construct or import a checked numeric-game/sign
   development, with birthdays and a visible size bound. Prove field and order
   laws, real closedness, normal forms, monomials, and compatibility of admissible
   sums. Then prove `found:thm:workspace`. The six surreal reports branch here:
   graph results need game representations; birthday and broadcast results
   need sign/ordinal arithmetic; evaluation and genetic-gap results need their
   specified supports or differentiation semantics. The plan's two tracks allow
   local Hahn mathematics to proceed before this bridge is finished.
6. **Topology and further structure (Layer E).** Define the intended fine
   topology over the actual carrier and prove small-index discreteness alongside
   the larger-index counterexample. Prove finite-angle lifting, distinguish
   derivative notions, and supply any real exponential/global character as
   separate proved structures. Only after a universe-coherent/class
   interpretation is established can full-class all-scale rigidity and its
   consequences be claimed.

This is a dependency order, not a promise to process reports in file order.
A substantial theorem should be split into its simplest necessary lemmas while
retaining an explicit obligation for every conclusion of the source theorem.

With nonnegative square roots proved, the remaining input to Mathlib's
`IsRealClosed.of_linearOrderedField` is the odd-degree polynomial root theorem.
Actual sign-field standard part, Conway monomials and weighted finite
coefficient scaling are now constructed. General finite-family coprime
factor linearization is a proved equivalence, using Mathlib’s Sylvester map
for the binary inverse. Translation to monic depressed form, the
actual polynomial scaling and reduction, and the ordinary-real coprime
factorization with a proper odd-degree factor are now constructed. The
binary lift in arbitrarily many formal parameters is now constructed as an actual
polynomial factorization over power series, with uniqueness, coprimeness and
exact degrees. Evaluation at finitely many positive-order Hahn inputs is a
proved algebra homomorphism with an explicit support certificate.
These constructions now give full finite-family, support-controlled coprime
factor lifting in arbitrary ordered Hahn fields, including the documented
common support monoid and unrestricted uniqueness. Strongly summable
evaluation inside the actual sign field remains unproved, so the Hahn lift
does not yet establish odd-degree-root existence in that field.
Conway's normalization and factor-lifting route is in
[*On Numbers and Games*, Theorems 23–28, pp. 40–42](https://kyl.neocities.org/books/%5BTEC%20CON%5D%20on%20numbers%20and%20games.pdf);
the universal ordered-field embedding there uses real closedness and cannot
be used circularly to obtain these roots. The finite-parameter strong-evaluation
bridge remains unproved. Small-index convergence in the native fine topology
cannot replace strong Hahn summability.

## Soundness boundaries that must survive translation

- **Permitted cuts:** a type in one universe cannot fill cuts indexed by its
  whole own carrier. Smaller-index cut data must remain explicit. The abstract
  obstruction does not by itself construct legitimate surreal cuts or prove
  `found:lem:bounds` for surreal numbers.
- **Complex multiplication:** the default product ring on `F × F` has the
  wrong multiplication and identity. Use the actual quadratic extension or a
  dedicated structure; see `found:rem:productring`.
- **Class versus workspace:** proving a theorem for a fixed Hahn field is useful
  but does not supply a universal field of all surreal numbers. Workspace
  localization and preservation of the operations used need separate proofs.
- **Two near-mirror series:** `found:ex:rescaling` uses coefficients `t^(-n²)`
  and fails evaluation at every nonzero argument in the fixed rational value
  group; `found:ex:internal` uses `t^(n²)` and is nonpolynomial despite internal
  all-scale coherence. Full-class rigidity cannot be specialized to a fixed
  value group without its missing dominating-scale hypothesis.
- **Strong sums:** well-ordered support and finite coefficient contributions
  are both required. Formal identities are not topological limits. Taylor
  lifting at `r + ε` uses the Taylor series centered at `r`, not unrestricted
  Maclaurin substitution (`found:rem:recentering`).
- **Different analytic categories:** radius-free coefficient germs, a fixed
  ordinary domain, common-domain germs, and formal coefficient series are
  distinct rings. The analysis merge records inequivalent function classes and
  inequivalent residues; a common name does not authorize a common definition.
- **Different geometries:** Hahn valuation and ordered modulus have distinct
  root and contour statements. A contour representing a residue series is an
  extra theorem, not the definition of the series functional.
- **Topology and size:** small-set discreteness (`found:thm:discrete`) coexists
  with a larger-index nonconstant convergent net (`found:ex:largerindex`). Do not
  assert eventual constancy for arbitrary index types or silently introduce an
  ordinary metric for the fine topology (`found:lem:nometric`).
- **Overlapping birthday results:** the two Gonshor reports prove the same
  inequality on different domains, neither containing the other. The shared
  `R[[ω⁻¹]]` case can reuse a proof once equivalence is established, but both
  domain statements remain obligations.
- **Independent proof notions:** fine derivative, formal power-series germ,
  Hahn-coherent datum and scalar-field derivation must retain separate types
  and explicit comparison theorems.

## Canonical report inventory

`T`, `L`, `P`, `C` mean literal `theorem`, `lemma`, `proposition` and
`corollary` environments; examples, computations, assessments and other
custom environments are not included. Paths below identify the 22 canonical
main texts present in the repository, including the two whose source is not
named `article.tex`. The document map and typeset catalogue may lag new batches.

| Main report source | T | L | P | C | Total |
|---|---:|---:|---:|---:|---:|
| [foundations-and-computation/computer-algebra/article.tex](foundations-and-computation/computer-algebra/article.tex) | 4 | 0 | 8 | 2 | 14 |
| [foundations-and-computation/foundations/article.tex](foundations-and-computation/foundations/article.tex) | 3 | 2 | 16 | 2 | 23 |
| [physics/surreal-scalars-and-spacetime/article.tex](physics/surreal-scalars-and-spacetime/article.tex) | 4 | 1 | 11 | 3 | 19 |
| [surcomplex/analysis/article.tex](surcomplex/analysis/article.tex) | 57 | 10 | 24 | 26 | 117 |
| [surcomplex/analytic-geometry/article.tex](surcomplex/analytic-geometry/article.tex) | 27 | 9 | 9 | 8 | 53 |
| [surcomplex/contours-and-stokes/article.tex](surcomplex/contours-and-stokes/article.tex) | 26 | 11 | 12 | 5 | 54 |
| [surcomplex/differential-equations/article.tex](surcomplex/differential-equations/article.tex) | 33 | 11 | 20 | 15 | 79 |
| [surcomplex/dynamics-and-normal-forms/article.tex](surcomplex/dynamics-and-normal-forms/article.tex) | 37 | 22 | 27 | 15 | 101 |
| [surcomplex/finite-deformations/article.tex](surcomplex/finite-deformations/article.tex) | 23 | 10 | 6 | 13 | 52 |
| [surcomplex/global-divisors/article.tex](surcomplex/global-divisors/article.tex) | 11 | 7 | 11 | 8 | 37 |
| [surcomplex/nonabelian-support/article.tex](surcomplex/nonabelian-support/article.tex) | 13 | 12 | 12 | 8 | 45 |
| [surcomplex/polynomial-algebra/article.tex](surcomplex/polynomial-algebra/article.tex) | 28 | 6 | 9 | 14 | 57 |
| [surcomplex/rank-one-berkovich/article.tex](surcomplex/rank-one-berkovich/article.tex) | 9 | 2 | 11 | 6 | 28 |
| [surcomplex/spectral-theory/article.tex](surcomplex/spectral-theory/article.tex) | 16 | 4 | 7 | 2 | 29 |
| [surcomplex/trigonometry/article.tex](surcomplex/trigonometry/article.tex) | 39 | 4 | 11 | 10 | 64 |
| [surquaternions/surquaternions/article.tex](surquaternions/surquaternions/article.tex) | 27 | 4 | 15 | 2 | 48 |
| [surreal/broadcast-sum-of-surreal-sequences/article.tex](surreal/broadcast-sum-of-surreal-sequences/article.tex) | 7 | 8 | 1 | 5 | 21 |
| [surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex](surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex) | 15 | 13 | 7 | 4 | 39 |
| [surreal/genetic-gaps-and-primitives/article.tex](surreal/genetic-gaps-and-primitives/article.tex) | 7 | 3 | 4 | 1 | 15 |
| [surreal/gonshor-laurent-birthdays/article.tex](surreal/gonshor-laurent-birthdays/article.tex) | 5 | 8 | 0 | 5 | 18 |
| [surreal/gonshor-product-birthdays/surreal_product_birthdays.tex](surreal/gonshor-product-birthdays/surreal_product_birthdays.tex) | 3 | 4 | 5 | 2 | 14 |
| [surreal/hahn-evaluation-at-omega/article.tex](surreal/hahn-evaluation-at-omega/article.tex) | 7 | 9 | 5 | 2 | 23 |
| **Total** | 401 | 160 | 231 | 158 | **950** |

The refresh after `796f8d4` adds four reports and expands an existing one.
Preserved manuscripts are counted independently of their merged reports;
these counts assert no equivalence or additional independent results.

| New or expanded report | Added main-report statements | New preserved manuscripts | Standard environments in those manuscripts |
|---|---:|---:|---:|
| [Surreal scalars and spacetime](physics/surreal-scalars-and-spacetime/article.tex) | 19 | 3 | 20 |
| [Dynamics and normal forms](surcomplex/dynamics-and-normal-forms/article.tex) | 101 | 6 | 115 |
| [Nonabelian support](surcomplex/nonabelian-support/article.tex) | 45 | 2 | 43 |
| [Surquaternions](surquaternions/surquaternions/article.tex) | 48 | 2 | 65 |
| [Contours and Stokes: untransformed Leray cycles](surcomplex/contours-and-stokes/sources/05-untransformed-leray-cycles.tex) | 19 | 1 | 21 |
| **Added** | **232** | **14** | **264** |

The 40 earlier preserved manuscripts contain 1075 standard environments; the
54 now present contain **1339** (654 theorems, 183 lemmas, 297 propositions,
205 corollaries). Their full statements and nonstandard claim environments
still require reconciliation. In particular, the physics report distinguishes
exact identities `[E]`, conditional mathematical theorems `[C]`, assessments
`[A]` and imported results `[I]`; this inventory does not turn an assessment
or a finite symbolic check into a Lean theorem.

**Retracted source claim:** the revised
[analytic-geometry ring comparison](surcomplex/analytic-geometry/article.tex)
withdraws the earlier Noetherian/maximal-ideal/regular-completion package for
the fixed-polydisk ring `O(D)((t^Γ))`. It claims that package only for the
three other named rings. The finite-deformations report supplies division,
finite freeness, multiplicity conservation and residue duality under its own
hypotheses, without a Noetherian assumption. Its positive coefficient ideal
is not finitely generated for nonzero divisible `Γ`; this observation concerns
the integral coefficient ring and does not say that the Hahn field itself is
non-Noetherian. The correction changes no standard-environment count.

## Main-report statement index

Every entry below is pending unless explicitly mapped to a checked declaration
in a later status update. Titles are copied from the LaTeX optional heading;
`Untitled` means the environment has no such heading. Labels are the exact
source labels, not Lean identifiers. An unlabeled statement is identified by
its source line. Line numbers are navigation hints for the current text; source
labels are the stable identifiers. This index does not include all mathematical
claims outside the four selected environments.

### computer-algebra

Source: [foundations-and-computation/computer-algebra/article.tex](foundations-and-computation/computer-algebra/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `cas:prop-countable` (line 557) | The finite-description bound |
| Theorem | `cas:thm-zerotest` (line 607) | Total coefficient access does not decide zero |
| Corollary | `cas:cor-sign` (line 659) | No universal three-way sign; equality reduces to zero testing |
| Corollary | `cas:cor-leading` (line 666) | No universal leading-term algorithm |
| Proposition | `cas:prop-validation` (line 692) | Unrestricted support validation is undecidable |
| Proposition | `cas:prop-leading` (line 712) | A high-rank leading-term and sign obstruction |
| Theorem | `cas:thm-core` (line 1070) | Effective rational monomial core |
| Theorem | `cas:thm-realclosure` (line 1189) | An implementable real-closed and algebraically closed layer |
| Theorem | `cas:thm-grid` (line 1417) | Finite extraction from a positive grid |
| Proposition | `cas:prop-precision` (line 1568) | Basic certified precision rules |
| Proposition | `cas:prop-finiteprefix` (line 1614) | Finite-prefix criterion for rank-one grids |
| Proposition | `cas:prop-lift` (line 2131) | Correctness of infinitesimal substitution |
| Proposition | `cas:prop-periods` (line 3376) | Every global extension acquires an infinite period |
| Proposition | `cas:prop-archimedean` (line 3733) | No order-preserving embedding |

### foundations

Source: [foundations-and-computation/foundations/article.tex](foundations-and-computation/foundations/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `found:prop:proper` (line 642) | There is no set of all surreal numbers |
| Proposition | `found:prop:allcuts` (line 695) | The unrestricted cut axiom is inconsistent |
| Lemma | `found:lem:bounds` (line 726) | Bounds for sets of surreals; the small positive lower bound |
| Proposition | `found:prop:incomplete` (line 771) | Untitled |
| Proposition | `found:prop:scott` (line 912) | Set codes for a definable class quotient |
| Proposition | `found:prop:recursion` (line 1202) | Local recursion and coherent assembly |
| Proposition | `found:prop:universe` (line 1325) | Why universe relativization avoids the cut contradiction |
| Proposition | `found:prop:universecut` (line 1344) | The missing self-cut |
| Proposition | `found:prop:closure` (line 1448) | Closure under a fixed set of finitary operations |
| Proposition | `found:prop:complex` (line 1542) | Finite data complexify safely |
| Theorem | `found:thm:workspace` (line 1690) | Workspace localization |
| Theorem | `found:thm:finitepoints` (line 1859) | Finite algebra over an algebraically closed base |
| Proposition | `found:prop:positive` (line 2025) | Support-local nonlinear recursion |
| Corollary | `found:cor:fixeddomain` (line 2058) | Fixed domain |
| Proposition | `found:ex:rescaling` (line 2182) | Universal rescaling fails in a fixed Hahn field |
| Proposition | `found:prop:rescalingpositive` (line 2210) | The enlarged group repairs it |
| Theorem | `found:thm:discrete` (line 2409) | Small subsets and small-index nets are discrete |
| Proposition | `found:prop:twotopologies` (line 2471) | Intrinsic and full-class subspace topologies differ |
| Lemma | `found:lem:nometric` (line 2510) | No countable ball basis is coinitial |
| Corollary | `found:cor:nopaths` (line 2568) | No nonconstant fine-continuous paths |
| Proposition | `found:prop:period` (line 2815) | Why an infinite period is not a paradox |
| Proposition | `found:prop:signtree` (line 2939) | Sign-tree categoricity |
| Proposition | `found:prop:univalence` (line 3358) | The elementary incompatibility test |

### surreal-scalars-and-spacetime

Source: [physics/surreal-scalars-and-spacetime/article.tex](physics/surreal-scalars-and-spacetime/article.tex).

All statements in this newly indexed report remain **pending**. The
`\TC` heading marker denotes a conditional mathematical claim; its stated
hypotheses must be retained. Exact computations, assessments and imported
physical results outside the four standard environments are separate claims.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `phys:prop:st` (line 847) | \TC\ Standard part |
| Proposition | `phys:prop:elementary` (line 872) | \TC\ Two elementary obstructions |
| Proposition | `phys:prop:discrete` (line 956) | \TC\ Set-sized collapse in the full fine topology |
| Proposition | `phys:prop:frame` (line 1165) | \TC\ Bounded-frame valuation invariance |
| Lemma | `phys:lem:balance` (line 1187) | \TC\ Dominant balance: the minimum is attained twice |
| Proposition | `phys:prop:pole` (line 1465) | \TC\ Route 1, valuation-theoretic: poles survive scalar extension and ramification |
| Proposition | `phys:prop:unlimited` (line 1492) | \TC\ Route 2, order-theoretic: a leading pole stays unlimited in every ordered extension |
| Corollary | `phys:cor:noext` (line 1534) | \TC\ The real-analytic geometric consequence |
| Proposition | `phys:prop:noendpoint` (line 1552) | \TC\ No field-valued Schwarzschild endpoint |
| Proposition | `phys:prop:crossover` (line 1909) | \TC\ The small-$J$ limit, uniform on bounded intervals |
| Theorem | `phys:thm:einstein` (line 2176) | {\TC\ Reduction of the Einstein tensor over $C^{\infty}(U,\R)[[h]]$} |
| Theorem | `phys:thm:reduction` (line 2233) | \TC\ Standard-part reduction over a Hahn coefficient algebra |
| Corollary | `phys:cor:shadow` (line 2275) | \TC\ Positive-order corrections cannot repair a singular shadow |
| Proposition | `phys:prop:matching` (line 2611) | \TC\ Outer and inner strong-summability criteria |
| Theorem | `phys:thm:spectral` (line 2699) | \TC\ Finite Hermitian spectral theorem |
| Theorem | `phys:thm:quantumshadow` (line 2738) | \TC\ Reduction of finite quantum protocols |
| Proposition | `phys:prop:phase` (line 2973) | \TC\ Canonical phase versus scalar differentiation |
| Corollary | `phys:cor:constantphase` (line 2991) | \TC\ The canonical global phase is constant in ordinary time |
| Proposition | `phys:prop:periods` (line 3011) | \TC\ Infinite periods of a global phase homomorphism |

### analysis

Source: [surcomplex/analysis/article.tex](surcomplex/analysis/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `a:prop:triangle` (line 186) | Modulus identities over an ordered field |
| Lemma | `a:lem:valbound` (line 291) | Crude valuation bound |
| Proposition | `a:prop:fragment` (line 358) | Containment of set-sized data |
| Lemma | `a:lem:neumann` (line 682) | Neumann support lemma |
| Corollary | `a:cor:complexsub` (line 723) | No growth condition |
| Theorem | `a:thm:discrete` (line 832) | Set-sized convergence collapses, with a uniform radius |
| Proposition | `a:prop:clopen` (line 876) | Clopen infinitesimal cosets |
| Corollary | `a:cor:nopath` (line 895) | No nonconstant continuous paths |
| Proposition | `b:inclusions` (line 1048) | The inclusions, and what witnesses them |
| Proposition | `b:fivefailures` (line 1118) | Five classical statements fail in the germ-analytic class |
| Proposition | `b:noremoval` (line 1193) | No unrestricted removability theorem |
| Proposition | `b:twistwitness` (line 1222) | The twisted-exponential witness |
| Theorem | `b:nogo` (line 1268) | Contour no-go |
| Corollary | `b:nogo-fundamental` (line 1298) | The fundamental theorem cannot be widened |
| Corollary | `b:log-not-coherent` (line 1307) | $\mathcal L$ is not a coherent primitive of $1/z$ |
| Corollary | `b:primitive-uniqueness-scope` (line 1320) | Uniqueness of primitives is a coherent statement |
| Lemma | `b:blocks` (line 1391) | Separated degree blocks |
| Theorem | `b:realization` (line 1461) | Realization of every formal series |
| Proposition | `b:remainder` (line 1501) | Uniform Taylor remainder |
| Corollary | `b:nogrowth` (line 1527) | No growth condition |
| Proposition | `b:globalseries` (line 1544) | Everywhere-summable means polynomial |
| Theorem | `b:germalgebra` (line 1574) | {The germ algebra is $\K[[X]]$} |
| Corollary | `b:isolated` (line 1638) | Isolated zeros of a germ |
| Theorem | `b:derivation-obstruction` (line 1681) | Derivation obstruction |
| Theorem | `b:CRgerm` (line 1733) | Cauchy--Riemann criterion for germs |
| Theorem | `b:harmonicgerm` (line 1768) | Harmonic conjugate germs |
| Theorem | `b:inverse` (line 1807) | Local inverse and implicit function theorems for germs |
| Theorem | `b:ramification` (line 1845) | Finite ramification normal form |
| Corollary | `b:localopen` (line 1875) | Local openness and no local modulus maximum |
| Corollary | `b:localidentity` (line 1916) | Local identity and maximum-modulus principles |
| Proposition | `b:formalprimitive` (line 1968) | The only local primitive obstruction |
| Theorem | `b:reschange` (line 1985) | Change of variable, with the ramification factor |
| Corollary | `b:localargument` (line 2007) | Local argument principle |
| Proposition | `b:formalres` (line 2016) | Formal residue facts and removability |
| Theorem | `b:lagrange` (line 2051) | Lagrange--B\"urmann inversion |
| Theorem | `c:p4:eval` (line 2262) | Faithful coherent evaluation |
| Corollary | `c:p4:shadow` (line 2316) | Leading coefficients control zero shadows |
| Theorem | `c:p4:monadtaylor` (line 2327) | Exact monad-wide Taylor expansion |
| Theorem | `c:p4:derivbridge` (line 2356) | The section derivative is the fine derivative |
| Proposition | `c:p4:prop-units` (line 2406) | Units |
| Proposition | `c:p4:prop-calculus` (line 2428) | Infinitesimal functional calculus |
| Theorem | `c:p4:composition` (line 2455) | Admissible composition |
| Proposition | `c:p4:chartchange` (line 2499) | Chart-change criterion |
| Theorem | `c:p4:identity` (line 2545) | Identity theorem for coherent sections |
| Theorem | `c:p4:gluing` (line 2611) | Gluing over the ordinary base |
| Theorem | `c:p4:lift` (line 2659) | Functoriality of the lift |
| Proposition | `c:p4:liftzeros` (line 2687) | A lift creates no displaced zeros |
| Theorem | `c:p4:bridge` (line 2731) | Scale embedding of arbitrary formal series |
| Proposition | `c:p4:obstruction` (line 2766) | An obstruction in the original chart |
| Proposition | `c:p5:calculus` (line 2844) | Elementary calculus of the functional |
| Lemma | `c:p5:positivity` (line 2902) | Positivity of the coefficientwise integral |
| Theorem | `c:p5:ML` (line 2927) | Surcomplex ML inequality |
| Theorem | `c:p5:cauchy` (line 2992) | Cauchy's theorem and integral formula |
| Corollary | `c:p5:cauchyest` (line 3046) | Cauchy estimates from a pointwise surreal bound |
| Corollary | `c:p5:scaledCauchy` (line 3070) | Cauchy estimates in an affine chart |
| Lemma | `c:p5:csmajorant` (line 3102) | Cauchy--Schwarz majorant lemma |
| Proposition | `c:p5:majorant` (line 3118) | Coefficientwise Cauchy estimate |
| Theorem | `c:p5:morera` (line 3161) | Coefficientwise Morera |
| Theorem | `c:p5:primitive` (line 3198) | Coherent primitives |
| Lemma | `d:lem:ordinarydivision` (line 3353) | Ordinary division, extended coefficientwise |
| Theorem | `d:thm:preparation` (line 3394) | Hahn--Weierstrass preparation, global form |
| Corollary | `d:cor:localprep` (line 3519) | Local preparation at a single zero |
| Theorem | `d:thm:division` (line 3557) | Hahn--Weierstrass division |
| Lemma | `d:lem:smallroots` (line 3595) | All corrections are infinitesimal |
| Theorem | `d:thm:zerocluster` (line 3622) | Exact zero clustering; specialization of the zero divisor |
| Corollary | `d:cor:displacement` (line 3696) | Simple-root lifting and its displacement |
| Theorem | `d:thm:rouchevaluation` (line 3745) | Valuation Rouch\'e: fibrewise stability |
| Theorem | `d:thm:rouchemargin` (line 3762) | Ordinary-margin Rouch\'e: stability of the total |
| Corollary | `d:cor:rouchereal` (line 3794) | Real-margin Rouch\'e: a surcomplex-valued hypothesis |
| Theorem | `d:thm:moments` (line 3852) | Contour moments of a zero cluster |
| Theorem | `d:thm:Hresidue` (line 4035) | Cluster residue theorem on $\Mc(U)$ |
| Proposition | `d:prop:quotientinM` (line 4094) | Quotients of coherent families lie in $\Mc(U)$ |
| Theorem | `d:thm:bridge1` (line 4124) | Residue-cluster theorem |
| Theorem | `d:thm:residuequotient` (line 4195) | Residue theorem for coherent quotients, global form |
| Theorem | `d:thm:bridge2` (line 4234) | Uniformly bounded pole order |
| Theorem | `d:thm:weightedarg` (line 4311) | Exact weighted argument principle |
| Corollary | `d:cor:zerosminuspoles` (line 4371) | Zeros minus poles |
| Theorem | `d:thm:deformation` (line 4405) | Deformation invariance under admissible infinitesimal deformations |
| Theorem | `d:thm:rationalresidue` (line 4461) | Global rational residue theorem |
| Lemma | `e:lem-normalize` (line 4560) | Infinitesimal rescaling; monomial radius |
| Theorem | `e:thm-openmapping` (line 4615) | Local finite degree and the open mapping theorem |
| Corollary | `e:cor-maxmod` (line 4644) | Strong local maximum modulus |
| Lemma | `e:lem-reversion` (line 4683) | Hahn reversion |
| Theorem | `e:thm-localinverse` (line 4716) | Coherent local inverse |
| Proposition | `e:prop-autobounded` (line 4750) | Automatic surreal boundedness |
| Theorem | `e:thm-realliouville` (line 4782) | Real-bounded macroscopically entire functions |
| Theorem | `e:thm-coeffliouville` (line 4825) | Coefficientwise growth and polynomial degree |
| Theorem | `e:thm-removable` (line 4883) | Coefficientwise removal is necessary and sufficient |
| Theorem | `e:thm-schwarzpick` (line 4938) | Schwarz--Pick for canonical lifts |
| Corollary | `e:cor-schwarz` (line 4986) | Schwarz lemma for canonical lifts |
| Corollary | `e:cor-spstability` (line 5001) | Stability away from the equality case |
| Theorem | `e:thm-biholo` (line 5048) | Lifting of infinitesimally deformed biholomorphisms |
| Corollary | `e:cor-liftbiholo` (line 5085) | Lifted conformal equivalence |
| Corollary | `e:cor-riemannmap` (line 5091) | Standard-halo Riemann mapping theorem |
| Theorem | `e:thm-montel` (line 5126) | Countable-support Montel theorem |
| Theorem | `e:thm-harmonic` (line 5188) | Coefficientwise harmonic conjugates |
| Theorem | `e:thm-poisson` (line 5214) | Poisson's formula and a coherent Dirichlet problem |
| Theorem | `e:thm-reflection` (line 5253) | Coherent Schwarz reflection |
| Proposition | `e:prop-infexp` (line 5305) | Infinitesimal exponential and logarithm |
| Proposition | `e:prop-polar` (line 5338) | The finite exponential and the polar form |
| Theorem | `e:thm-exp` (line 5401) | Properties of the canonical exponential |
| Theorem | `e:thm-twisted` (line 5488) | The twisted global exponentials |
| Corollary | `e:cor-twistwitness` (line 5544) | A structured unit-modulus witness |
| Theorem | `e:thm-periodobstruction` (line 5566) | The period obstruction |
| Theorem | `e:thm-globallog` (line 5619) | A logarithm on the whole punctured class plane |
| Corollary | `e:cor-lognotcoherent` (line 5663) | $\mathcal L$ is not a coherent primitive of $1/z$ |
| Theorem | `e:thm-principallog` (line 5712) | Principal logarithm on the cut plane |
| Proposition | `e:prop-logdiscrepancy` (line 5738) | $\mathcal L$ and $\Log$ are different functions |
| Theorem | `e:thm-logcharts` (line 5782) | Logarithm charts on multiplicative monads |
| Theorem | `e:thm-picard` (line 5818) | Every nonzero value at every surreal scale |
| Theorem | `f:thm-affine` (line 5937) | Affine transport of the coherent theory |
| Proposition | `f:prop-chartchange` (line 6030) | Chart-change criterion |
| Corollary | `f:cor-scaledCauchy` (line 6084) | Cauchy estimates at an arbitrary coherent scale |
| Theorem | `f:thm-rigidity` (line 6156) | All-scale polynomial rigidity |
| Corollary | `f:cor-globalclassical` (line 6219) | Global classical consequences in the rigid category |
| Lemma | `f:lem-polefree` (line 6281) | A pole-free coherent fraction is coherent holomorphic |
| Theorem | `f:thm-rationalrigidity` (line 6335) | All-scale rational rigidity |

### analytic-geometry

Source: [surcomplex/analytic-geometry/article.tex](surcomplex/analytic-geometry/article.tex).

The fixed-polydisk package previously attributed in the prose is retracted;
see the canonical inventory note above. The 53 standard environments below
retain their own ring hypotheses.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `analytic:thm:overview-structure-A` (line 276) | Structure of the radius-free ring $\A_n$, overview |
| Theorem | `analytic:thm:overview-structure-R` (line 289) | Structure and finite maps for the common-domain ring $\RR_n$, overview |
| Theorem | `analytic:thm:overview-deform` (line 301) | Conservation, duality and the radius-free strengthening, overview |
| Theorem | `analytic:thm:overview-stability` (line 322) | Quantitative stability over $\A_n$, overview |
| Lemma | `analytic:lem:enlargement` (line 463) | Enlargement rule |
| Lemma | `analytic:lem:neumann` (line 496) | Hahn--Neumann support lemma |
| Lemma | `analytic:lem:operator` (line 525) | Positive-support operator inversion |
| Proposition | `analytic:prop:units` (line 620) | Units of $\A_n$ |
| Proposition | `analytic:prop:translation` (line 633) | Evaluation and translation over $\A_n$ |
| Proposition | `analytic:prop:kernels` (line 666) | Evaluation kernels and finite jets over $\A_n$ |
| Proposition | `analytic:prop:faithful` (line 687) | Faithful interpretation as functions on the monad |
| Proposition | `analytic:prop:evaluationR` (line 747) | Evaluation, support and translation over $\RR_n$ |
| Lemma | `analytic:lem:density` (line 784) | Infinitesimal evaluation detects nonzero elements of $\RR_n$ |
| Theorem | `analytic:thm:divisionA` (line 881) | Hahn-germ division over $\A_n$ |
| Theorem | `analytic:thm:prepA` (line 910) | Preparation and finite projection over $\A_n$ |
| Corollary | `analytic:cor:hypersurface-fiber` (line 947) | Fibres of a prepared hypersurface over $\A_n$ |
| Theorem | `analytic:thm:prepR` (line 995) | Parameterized Hahn preparation over $\RR_n$ |
| Theorem | `analytic:thm:divisionR` (line 1035) | Parameterized Hahn division over $\RR_n$ |
| Corollary | `analytic:cor:freehypersurfaceR` (line 1061) | Finite free hypersurface quotient over $\RR_n$ |
| Theorem | `analytic:thm:noetherianA` (line 1099) | Noetherianity of $\A_n$ |
| Theorem | `analytic:thm:weak-nullA` (line 1114) | Weak Nullstellensatz over $\A_n$ |
| Theorem | `analytic:thm:strong-nullA` (line 1144) | Jacobson property and strong Nullstellensatz over $\A_n$ |
| Theorem | `analytic:thm:regularA` (line 1176) | Local geometry of $\A_n$ |
| Theorem | `analytic:thm:noetherianR` (line 1226) | Noetherian monad ring $\RR_n$ |
| Proposition | `analytic:prop:normalization` (line 1255) | Noether normalization over $\RR_n$ |
| Theorem | `analytic:thm:weaknullR` (line 1279) | Weak monad Nullstellensatz over $\RR_n$ |
| Theorem | `analytic:thm:strongnullR` (line 1305) | Strong monad Nullstellensatz over $\RR_n$ |
| Proposition | `analytic:prop:completionR` (line 1348) | Local coordinates and completion over $\RR_n$ |
| Theorem | `analytic:thm:finitemap` (line 1394) | Finite projection and generic fibres over $\RR_n$ |
| Lemma | `analytic:lem:residue-annihilate` (line 1602) | Well-definedness and annihilation over $\A_n$ |
| Lemma | `analytic:lem:spanning` (line 1638) | Spanning with a support certificate, over $\A_n$ |
| Theorem | `analytic:thm:finite-deformA` (line 1659) | Finite complete-intersection deformation over $\A_n$: the radius-free strengthening |
| Theorem | `analytic:thm:conjugacy` (line 1751) | Positive Hahn conjugacy |
| Lemma | `analytic:lem:ordinarykoszul` (line 1794) | Ordinary contraction on one fixed neighbourhood |
| Theorem | `analytic:thm:conservationR` (line 1837) | Support-explicit conservation of multiplicity over $\RR_n$ |
| Corollary | `analytic:cor:matrices` (line 1917) | Infinitesimal coordinate eigenvalues |
| Theorem | `analytic:thm:residueduality` (line 1973) | Support-controlled residue duality over $\RR_n$ |
| Proposition | `analytic:prop:residues-agree` (line 2022) | The two residue functionals agree where both are defined |
| Corollary | `analytic:cor:residueframe` (line 2045) | A support-controlled constant residue frame |
| Lemma | `analytic:lem:finite-dependency` (line 2082) | Finite dependency at a prescribed exponent |
| Theorem | `analytic:thm:trace` (line 2103) | Trace--Jacobian identity |
| Theorem | `analytic:thm:zeros` (line 2155) | Conservation of singular zeros |
| Proposition | `analytic:prop:jacobian` (line 2202) | Four equivalent forms of the simple-root criterion |
| Corollary | `analytic:cor:weighted` (line 2217) | Weighted evaluation and simple residues |
| Theorem | `analytic:thm:workspace` (line 2270) | Workspace invariance over $\A_n$ |
| Theorem | `analytic:thm:basechange` (line 2300) | Base change and full surcomplex exhaustiveness over $\RR_n$ |
| Corollary | `analytic:cor:full-sc` (line 2332) | Full-surcomplex conservation |
| Theorem | `analytic:thm:formal-comparison` (line 2385) | Analytic--formal comparison |
| Lemma | `analytic:lem:scaled-polynomial` (line 2467) | Scaled Taylor polynomials at each Hahn exponent |
| Theorem | `analytic:thm:local-stability` (line 2485) | One-root Hensel--Rouch\'e bound over $\A_n$ |
| Corollary | `analytic:cor:separation` (line 2542) | Separation of simple zeros |
| Theorem | `analytic:thm:cluster-stability` (line 2559) | Finite-cluster correspondence |
| Corollary | `analytic:cor:nonpolynomial` (line 2997) | A nonpolynomial length-five cluster over $\RR_2$ |

### contours-and-stokes

Source: [surcomplex/contours-and-stokes/article.tex](surcomplex/contours-and-stokes/article.tex).

The expansion adds 19 standard environments for untransformed Leray cycles.
Those obligations remain **pending** and retain a convergent isolated leading
map, a positive lower bound on perturbation support and the specified ordinary
covering-cycle category. They do not remove the determinant factors from the
earlier transformed coordinate-torus formulas or assert fine-continuous cycles.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `contours:lem:support` (line 431) | Support mechanism |
| Proposition | `contours:prop:fullfine` (line 630) | Full-class discreteness of sets |
| Proposition | `contours:prop:intrinsic` (line 661) | Intrinsic total separation |
| Proposition | `contours:prop:noftc` (line 711) | No endpoint integration for all fine-local primitives |
| Proposition | `contours:prop:mesh` (line 749) | Finite-partition obstruction |
| Theorem | `contours:thm:stdpartjordan` (line 807) | Jordan separation in the standard-part topology |
| Theorem | `contours:thm:sajordan` (line 881) | Semialgebraic Jordan theorem; classical input |
| Theorem | `contours:thm:polstokes` (line 1024) | Polynomial-chain Stokes |
| Theorem | `contours:thm:hahnstokes` (line 1117) | Hahn-valued generalized Stokes |
| Proposition | `contours:prop:poincare` (line 1166) | Support-preserving Poincar\'e lemma |
| Theorem | `contours:thm:cohomology` (line 1188) | Cohomology of the globally supported Hahn complex |
| Lemma | `contours:lem:pullback` (line 1335) | Pullback and differential with a support certificate |
| Theorem | `contours:thm:deformedstokes` (line 1396) | Stokes for Hahn-deformed chains |
| Theorem | `contours:thm:homotopy` (line 1491) | Hahn homotopy formula |
| Proposition | `contours:prop:ml` (line 1538) | An order-valued parameter estimate |
| Theorem | `contours:thm:cauchy` (line 1599) | Coherent Cauchy theorem |
| Theorem | `contours:thm:endpoints` (line 1637) | Exact endpoint-transport formula |
| Theorem | `contours:thm:winding` (line 1714) | Winding stability at one scale |
| Theorem | `contours:thm:cauchyformula` (line 1747) | Cauchy formula at displaced points and on deformed contours |
| Corollary | `contours:cor:deformedres` (line 1817) | Residues on a deformed protecting contour |
| Proposition | `contours:prop:overlap` (line 1892) | Agreement on admissible overlaps |
| Theorem | `contours:thm:rescaling` (line 1983) | Positive rescaling gives polynomial coefficient families |
| Theorem | `contours:thm:localcauchy` (line 2050) | Cauchy formula for a radius-free germ |
| Lemma | `contours:lem:protect` (line 2083) | A radius protecting an entire one-variable cluster |
| Theorem | `contours:thm:microcircle` (line 2107) | Microscopic circle realization of the one-variable perturbation residue |
| Theorem | `contours:thm:localresidue` (line 2155) | Radius-free moving-pole residue theorem |
| Theorem | `contours:thm:microtorus` (line 2264) | Coordinate-power torus realization |
| Lemma | `contours:lem:residuetransform` (line 2352) | Transformation of the Hahn perturbation residue |
| Theorem | `contours:thm:generalrepresentation` (line 2390) | Microscopic contour representation of a general residue |
| Theorem | `contours:thm:septorus` (line 2540) | Separating-torus realization; conditional on \cite{Geometry} |
| Lemma | `contours:lem:radiusfreesub` (line 2876) | Radius-free substitution into a Hahn map |
| Corollary | `contours:cor:radialeval` (line 2914) | Radial evaluation of an ordinary family |
| Lemma | `contours:lem:positiveimplicit` (line 2945) | Positive implicit equation |
| Lemma | `contours:lem:targetmonomial` (line 3021) | A discriminant-avoiding monomial direction in the \emph{target} |
| Theorem | `contours:thm:ramifiedleray` (line 3059) | Ramified Leray family; ordinary analysis |
| Lemma | `contours:lem:constantperiod` (line 3125) | Coefficientwise constant-period identity |
| Proposition | `contours:prop:admissiblepullback` (line 3197) | Admissibility of the untransformed pullback |
| Theorem | `contours:thm:untransformed` (line 3244) | Universal untransformed contour |
| Corollary | `contours:cor:scalecancel` (line 3300) | Cancellation of the auxiliary scales |
| Lemma | `contours:lem:radialbounds` (line 3371) | Finite radial bounds |
| Theorem | `contours:thm:adaptedlift` (line 3441) | Equation-adapted lift on the same cover |
| Corollary | `contours:cor:protectedsheets` (line 3497) | Regular protected sheets |
| Lemma | `contours:lem:straighthomotopy` (line 3543) | Admissible straight homotopy |
| Theorem | `contours:thm:untransformedhomotopy` (line 3570) | Untransformed homotopy invariance |
| Theorem | `contours:thm:degreenormalization` (line 3615) | Degree normalization on the adapted cycle |
| Corollary | `contours:cor:protectedtrace` (line 3657) | Protected trace representation |
| Proposition | `contours:prop:idealannihilation` (line 3689) | Annihilation of the equation ideal, and descent |
| Lemma | `contours:lem:finitejet` (line 3732) | Finite-jet extension of an ordinary local residue |
| Theorem | `contours:thm:formalcontour` (line 3757) | Formal-coefficient contour theorem |
| Theorem | `contours:thm:algpairing` (line 4223) | Characterization and algebraic Cauchy theory |
| Proposition | `contours:prop:rationalcohomology` (line 4276) | Rational de Rham quotient |
| Proposition | `contours:prop:comparison` (line 4321) | Comparison on separated charts |
| Proposition | `contours:prop:samplingcriterion` (line 4438) | A precise sampling criterion |
| Theorem | `contours:thm:sampling` (line 4483) | Coefficientwise recovery of a Hahn contour |

### differential-equations

Source: [surcomplex/differential-equations/article.tex](surcomplex/differential-equations/article.tex).

All statements in this newly indexed report remain **pending**.

**Needs correction:** the prose warning `diff:warn:collapse` and the two
README summaries say that replacing `∂O` by `O` makes the criterion
"`b` infinitesimal." Since `O` is defined as the finite surreals, that
replacement instead makes the criterion "`b` finite." The displayed
infinitesimal counterexample refutes either weakened criterion. This
wording issue does not establish or refute the pending logarithmic-derivative
image theorem; the source manuscripts and generated PDF are unchanged.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `diff:lem:neumann` (line 456) | Positive-support calculus |
| Theorem | `diff:thm:BM` (line 498) | Berarducci--Mantova: imported input |
| Proposition | `diff:prop:algdiff` (line 587) | Algebraic implicit differentiation |
| Proposition | `diff:prop:complexification` (line 608) | Unique extension to $\SC$ |
| Proposition | `diff:prop:realexp` (line 657) | Real exponential integration |
| Lemma | `diff:lem:smallnegative` (line 681) | Order reversal on infinitesimals, and smallness |
| Proposition | `diff:prop:coarse` (line 738) | A preliminary obstruction |
| Proposition | `diff:prop:rescale` (line 886) | Change of independent scale changes the solvability data |
| Proposition | `diff:prop:totalchain` (line 904) | The two formal derivations commute; the valid polynomial chain rule |
| Proposition | `diff:prop:chain` (line 939) | Two-derivative chain rule for series, with derived summability |
| Lemma | `diff:lem:smallchain` (line 1186) | Formal identities survive infinitesimal evaluation |
| Theorem | `diff:thm:unitphase` (line 1263) | Unique infinitesimal phase residue |
| Theorem | `diff:thm:cisgroup` (line 1311) | Finite-angle phase group, with its differential identity |
| Corollary | `diff:cor:polar` (line 1361) | Branch-free polar form |
| Proposition | `diff:prop:normprimitive` (line 1417) | Normalized primitive |
| Proposition | `diff:prop:RB` (line 1459) | Integration by parts, and a Rota--Baxter correction |
| Theorem | `diff:thm:idealstructure` (line 1523) | Structure of the bounded-primitive ideal |
| Theorem | `diff:thm:logimage` (line 1635) | Exact logarithmic-derivative image |
| Theorem | `diff:thm:phasecriterion` (line 1691) | Finite-primitive criterion for rank-one equations |
| Corollary | `diff:cor:oscillator` (line 1769) | The missing oscillator |
| Corollary | `diff:cor:rotation` (line 1833) | The unit-circle version |
| Corollary | `diff:cor:riccati` (line 1853) | A Riccati transfer |
| Theorem | `diff:thm:gauge` (line 1906) | Purely infinite phase normal form, with uniqueness |
| Corollary | `diff:cor:exact` (line 1950) | Obstruction exact sequence |
| Corollary | `diff:cor:tensor` (line 1980) | Tensor, dual, and no finite-order obstruction |
| Theorem | `diff:thm:power` (line 2027) | Sharp support threshold |
| Corollary | `diff:cor:power` (line 2070) | Power threshold |
| Corollary | `diff:cor:logscales` (line 2086) | Iterated-logarithm thresholds at every finite depth |
| Theorem | `diff:thm:rational` (line 2178) | Rational phase criterion |
| Theorem | `diff:thm:strip` (line 2299) | The strip exponential |
| Theorem | `diff:thm:maximalstrip` (line 2336) | Exact domain of the exponential differential equation |
| Theorem | `diff:thm:maximalstripalt` (line 2348) | Maximality restated |
| Corollary | `diff:cor:noglobalPsi` (line 2381) | Phase-independent nonexistence |
| Proposition | `diff:prop:defect` (line 2411) | Character-independent invariant defect |
| Theorem | `diff:thm:variation` (line 2495) | Variation of constants |
| Proposition | `diff:prop:polyforcing` (line 2545) | Polynomial forcing, and a terminating inverse |
| Lemma | `diff:lem:kernels` (line 2586) | Kernels of powers and real shifts |
| Theorem | `diff:thm:constant` (line 2617) | Constant-coefficient solution classification |
| Corollary | `diff:cor:matrix` (line 2691) | Constant matrix systems |
| Theorem | `diff:thm:triangular` (line 2732) | Triangular fundamental-matrix criterion |
| Proposition | `diff:prop:trace` (line 2768) | The trace test is necessary and not sufficient |
| Proposition | `diff:prop:hahnderiv` (line 2807) | The derivation on a real-exponent workspace |
| Corollary | `diff:cor:valphase` (line 2877) | A valuation test, on real exponents only |
| Theorem | `diff:thm:resolvent` (line 2910) | First-order resolvent on a real-exponent workspace |
| Proposition | `diff:prop:polyresolvent` (line 2952) | Polynomial Laurent inverse |
| Proposition | `diff:prop:factorialambiguity` (line 3036) | Uniqueness depends on the ambient field |
| Theorem | `diff:thm:factorial` (line 3064) | An exact factorially divergent forced oscillator |
| Theorem | `diff:thm:Hahnintegral` (line 3149) | Exact derivative image: one resonant coefficient |
| Theorem | `diff:thm:Hahnlogder` (line 3171) | Exact logarithmic-derivative image in $\Hring$ |
| Proposition | `diff:prop:Hahnambient` (line 3204) | Workspace versus ambient |
| Lemma | `diff:lem:monomialcriterion` (line 3290) | Monomial criterion |
| Theorem | `diff:thm:hull` (line 3310) | Differential Hahn hull |
| Proposition | `diff:prop:realgroup` (line 3370) | The real-exponent case, exactly |
| Theorem | `diff:thm:localize` (line 3410) | Closure localization |
| Theorem | `diff:thm:PVone` (line 3539) | Adjoining one missing rank-one solution |
| Theorem | `diff:thm:extension` (line 3583) | The same extension, with differential simplicity |
| Theorem | `diff:thm:PVlocal` (line 3627) | Over a localized workspace |
| Theorem | `diff:thm:PVhahn` (line 3652) | Over the rational Hahn field |
| Theorem | `diff:thm:PVrational` (line 3698) | Over the rational function field $\C(X)$ |
| Lemma | `diff:lem:rationallogder` (line 3708) | Untitled |
| Corollary | `diff:cor:nonembedding` (line 3737) | No differential embedding |
| Proposition | `diff:prop:oscillatorExtension` (line 3806) | A genuine oscillator |
| Theorem | `diff:thm:orderobstruction` (line 3868) | Oscillation cannot retain the $H$-field ordering rule |
| Lemma | `diff:lem:saturated` (line 3915) | The lattice is saturated |
| Theorem | `diff:thm:torus` (line 3928) | The diagonal phase torus |
| Theorem | `diff:thm:coherentlinear` (line 4194) | Positive-perturbation fundamental matrix |
| Corollary | `diff:cor:coherentinhom` (line 4259) | Inhomogeneous coherent systems |
| Corollary | `diff:cor:determinant` (line 4277) | Liouville determinant identity |
| Proposition | `diff:prop:negativecoherent` (line 4294) | A negative leading exponent forbids a coherent scalar exponential |
| Lemma | `diff:lem:nonlinear` (line 4361) | Admissibility of nonlinear evaluation |
| Theorem | `diff:thm:ivp` (line 4391) | Support-certified positive-support initial-value problem |
| Theorem | `diff:thm:monodromy` (line 4586) | Monodromy valued in $\GL_{d}(K_{\Gamma})$ |
| Proposition | `diff:prop:formalrecursion` (line 4715) | Formal existence over any characteristic-zero field |
| Lemma | `diff:lem:finiteincoming` (line 4768) | Finite incoming contributions |
| Theorem | `diff:thm:coefderivation` (line 4782) | Differentiation preserves common-domain coherence |
| Theorem | `diff:thm:totalchainhalo` (line 4830) | Total intrinsic derivative of an evaluation |
| Corollary | `diff:cor:naturality` (line 4895) | Coefficientwise linear naturality |
| Lemma | `diff:lem:twosupports` (line 5864) | Sum of two supports |
| Lemma | `diff:lem:higman` (line 5893) | Finite-word lemma |

### dynamics-and-normal-forms

Source: [surcomplex/dynamics-and-normal-forms/article.tex](surcomplex/dynamics-and-normal-forms/article.tex).

Statements in this newly indexed report remain **pending unless mapped above**.
The full finite-word Neumann support lemma is now checked; the correction
below also has a checked Hahn-series counterexample.

**Needs correction:** `dyn:cor:ancestry` allows arbitrary Hahn input `A` but
bounds the number of positive-support operator applications contributing at
exponent `γ` by `ell_S(γ)`, and limits input data to `D_S(γ)`. The surrounding
Hahn-series convention permits arbitrary well-ordered supports; no
nonnegative-input restriction is supplied. Take `Γ = ℤ`, `S = {1}`,
`T(B) = t B`, and `A = t^(-100)`: `T^100(A) = 1` contributes at `γ = 0`,
where `ell_S(0) = 0`. The coefficientwise finiteness statement instead needs
the finitely many pairs of an input exponent `a` and an `S`-word summing to
`γ - a`, as in the preceding `dyn:lem:neumann`. The corollary's proof invokes
that lemma but does not justify its stronger absolute bound. The identity
and impossibility of any input-independent bound at output zero are now
checked in [Ancestry.lean](../Surreal/HahnSeries/Ancestry.lean). The later
`dyn:prop:linearization` uses the narrower input `L⁻¹f` with
`S = supp f > 0`; its proof explicitly counts an initial support letter, so
this counterexample does not refute that specialized bound or the associated
classification theorem. Those downstream obligations still require separate
proofs; no source text has been silently changed here.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `dyn:lem:neumann` (line 847) | Positive-support lemma of Neumann, in finite-word form |
| Corollary | `dyn:cor:ancestry` (line 890) | Finite ancestry |
| Lemma | `dyn:lem:evaluation` (line 966) | Evaluation, inversion, isometry |
| Proposition | `dyn:prop:eval` (line 1026) | Faithful analytic realization |
| Lemma | `dyn:lem:faithful` (line 1059) | Faithfulness of infinitesimal evaluation |
| Proposition | `dyn:prop:subgroup` (line 1098) | Substitution group |
| Lemma | `dyn:lem:inverse` (line 1145) | Near-identity inverses |
| Theorem | `dyn:thm:exp-log` (line 1175) | Same-domain exponential--logarithm correspondence |
| Lemma | `dyn:lem:fixedderivative` (line 1261) | Derivative of the logarithmic generator at an ordinary fixed point |
| Corollary | `dyn:cor:julia` (line 1283) | Julia equation |
| Proposition | `dyn:prop:intertwine` (line 1292) | Conjugacy and vector fields |
| Corollary | `dyn:cor:flow` (line 1306) | Exact flow law and admissible Hahn times |
| Corollary | `dyn:cor:roots` (line 1339) | Unique fractional iteration; torsion-freeness |
| Theorem | `dyn:thm:fixed-ideal` (line 1359) | Fixed-point ideal of a positive flow |
| Theorem | `dyn:thm:centralizer` (line 1409) | The full positive centralizer in one variable |
| Proposition | `dyn:prop:workspace` (line 1473) | Workspace invariance |
| Lemma | `dyn:lem:radius-loss` (line 1526) | Single-step analytic loss |
| Lemma | `dyn:lem:sharp-divisor` (line 1546) | Sharpness and analytic failure |
| Proposition | `dyn:prop:norm` (line 1589) | A compact-disk estimate, offered only as a starting point |
| Theorem | `dyn:thm:main` (line 1624) | Universal coefficient-category classification |
| Proposition | `dyn:prop:linearization` (line 1683) | Support-controlled inverse; route A |
| Theorem | `dyn:thm:lifting` (line 1722) | Support-controlled lifting; route B, drift permitted |
| Proposition | `dyn:prop:reusable` (line 1806) | Reusable abstract form |
| Proposition | `dyn:prop:first-weight` (line 1831) | The first-weight obstruction |
| Corollary | `dyn:cor:entirethreshold` (line 1881) | The entire-coefficient threshold; polynomial universality |
| Theorem | `dyn:thm:radius-depth` (line 1898) | Radius at a specified Hahn exponent |
| Theorem | `dyn:thm:degrees` (line 1937) | Polynomial coefficient degrees |
| Proposition | `dyn:prop:halo` (line 1983) | Actual conjugacy on a finite halo |
| Proposition | `dyn:prop:monad` (line 2002) | The monad needs no arithmetic |
| Lemma | `dyn:lem:multihomological` (line 2040) | Multivariable homological inverse |
| Theorem | `dyn:thm:multilifting` (line 2056) | Multivariable support-controlled lifting |
| Theorem | `dyn:thm:commoncoord` (line 2091) | A common coordinate for the centralizer |
| Lemma | `dyn:lem:jets` (line 2190) | Uniform reciprocal-jet estimates |
| Theorem | `dyn:thm:collapse` (line 2220) | Exact coefficient-radius collapse; requires drift |
| Corollary | `dyn:cor:finitefailure` (line 2283) | A finite-support instability |
| Theorem | `dyn:thm:trichotomy` (line 2291) | The common-domain / radius-free trichotomy |
| Theorem | `dyn:thm:multicollapse` (line 2348) | Exact multivariable radius collapse |
| Proposition | `dyn:prop:cf` (line 2405) | Continued-fraction formula |
| Theorem | `dyn:thm:nonbrjuno` (line 2438) | Explicit arithmetic separations |
| Lemma | `dyn:lem:nonresonant` (line 2565) | Nonresonant residue |
| Lemma | `dyn:lem:displacement` (line 2594) | Divisible displacement: cancelling a common infinitesimal divisor |
| Lemma | `dyn:lem:root-count` (line 2630) | Roots on the unit shell |
| Theorem | `dyn:thm:exact` (line 2658) | Exact finite-return linearization |
| Theorem | `dyn:thm:shell` (line 2772) | Resonant shell cycles |
| Corollary | `dyn:cor:finite-certificate` (line 2818) | A finite obstruction certificate |
| Theorem | `dyn:thm:stability` (line 2834) | Stability above the first return face |
| Theorem | `dyn:thm:coherent` (line 2897) | Coherent realization of resonant linearization |
| Proposition | `dyn:prop:leading` (line 3002) | The leading-coefficient exponential integral |
| Proposition | `dyn:prop:noncoherent` (line 3068) | A divergent ordinary linearizer survives on the monad |
| Theorem | `dyn:thm:workspace` (line 3115) | Workspace invariance for the finite-return package |
| Corollary | `dyn:cor:surcomplex` (line 3144) | Transfer to the surcomplex numbers |
| Theorem | `dyn:thm:phase` (line 3253) | Cancellation phase diagram |
| Lemma | `dyn:lem:unit` (line 3404) | A sufficient unit criterion |
| Theorem | `dyn:thm:common` (line 3422) | Common-domain Hahn linearization |
| Corollary | `dyn:cor:universal` (line 3498) | Universal leading profile at a resonant scale |
| Proposition | `dyn:prop:factorV` (line 3537) | The generator gains no new pole |
| Lemma | `dyn:lem:residue` (line 3575) | Exact residue at a simple fixed point |
| Proposition | `dyn:prop:firstcorrection` (line 3595) | The first correction is an explicit logarithm |
| Corollary | `dyn:cor:factorization` (line 3615) | Separation of the branching factors |
| Lemma | `dyn:lem:torsion` (line 3648) | An infinitesimal phase has no torsion |
| Theorem | `dyn:thm:monodromy` (line 3669) | Exact monodromy and obstruction to finite ramification |
| Lemma | `dyn:lem:slopes` (line 3704) | A nonlinear polynomial cannot have one slope at all its zeros |
| Lemma | `dyn:lem:reduction` (line 3719) | Reduction of an algebraic Hahn element |
| Lemma | `dyn:lem:essential` (line 3733) | A higher-order logarithmic pole forces transcendence |
| Theorem | `dyn:thm:dichotomy` (line 3752) | Polynomial Euler maps: the algebraicity dichotomy |
| Proposition | `dyn:prop:leadingalgebraic` (line 3815) | Classification of algebraic leading coordinates |
| Proposition | `dyn:prop:recurrence` (line 3903) | Exact finite recurrence |
| Theorem | `dyn:thm:sharp` (line 3932) | Sharp domain and valuative isometry |
| Theorem | `dyn:thm:modelfactor` (line 4032) | All-orders factorization and finite-cover obstruction for the model |
| Proposition | `dyn:prop:second` (line 4070) | Explicit second-order expansion |
| Lemma | `dyn:lem:primitive` (line 4169) | Support-preserving primitives |
| Lemma | `dyn:lem:homotopy` (line 4199) | Explicit exactness of an infinitesimal pullback |
| Proposition | `dyn:prop:time-conjugacy` (line 4233) | Time forms under conjugacy |
| Theorem | `dyn:thm:difference` (line 4256) | Discrete equation as a primitive problem |
| Corollary | `dyn:cor:abel` (line 4302) | Exact global Abel criterion |
| Theorem | `dyn:thm:exact-sequence` (line 4325) | Complete finite-dimensional discrete obstruction |
| Lemma | `dyn:lem:displacement2` (line 4402) | Implicit displacement lemma |
| Theorem | `dyn:thm:classification` (line 4450) | Complete period invariant and marked conjugacy |
| Corollary | `dyn:cor:simplyconnected` (line 4491) | Simply connected domains |
| Theorem | `dyn:thm:moduli` (line 4524) | An explicit moduli space |
| Theorem | `dyn:thm:flat` (line 4598) | Flatly indistinguishable but globally nonconjugate |
| Proposition | `dyn:prop:euler-residue` (line 4719) | Exact residue of the Euler time form |
| Corollary | `dyn:cor:euler-normal` (line 4777) | A global coherent normal form for the Euler family |
| Theorem | `dyn:thm:slowtime` (line 4856) | Common-chart Hahn lifting of the slow flow |
| Proposition | `dyn:prop:inverse` (line 4980) | Positive near-identity maps |
| Proposition | `dyn:prop:exp` (line 5004) | Supported Hamiltonian exponential |
| Lemma | `dyn:lem:projection` (line 5062) | Entire action projection |
| Theorem | `dyn:thm:homological` (line 5082) | Sharp homological criterion |
| Theorem | `dyn:thm:normalform` (line 5130) | Exact positive-Hahn normal form |
| Corollary | `dyn:cor:hamsurcomplex` (line 5231) | Finite surcomplex phase space |
| Theorem | `dyn:thm:integrability` (line 5259) | Exact integrability |
| Theorem | `dyn:thm:pcentralizer` (line 5280) | Poisson centralizer |
| Proposition | `dyn:prop:flow` (line 5322) | Exact ordinary-time evolution |
| Theorem | `dyn:thm:universal` (line 5360) | Sharp universal normalization criterion |
| Proposition | `dyn:prop:explicitbad` (line 5401) | An explicit super-Liouville obstruction |
| Theorem | `dyn:thm:rescale` (line 5516) | Compatible support-certified domains |
| Corollary | `dyn:cor:homogeneous` (line 5588) | A degree-dependent radius |
| Proposition | `dyn:prop:discrete` (line 5744) | Polynomial-layer linearization |
| Theorem | `dyn:thm:finite-order` (line 5792) | Same-domain finite-order decomposition |
| Proposition | `dyn:prop:quadratic-scale` (line 5875) | Quadratic scaling and the boundary of the halo theorem |
| Proposition | `dyn:prop:critical` (line 5918) | A precise rescaled-germ obstruction |

### finite-deformations

Source: [surcomplex/finite-deformations/article.tex](surcomplex/finite-deformations/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `finite:lem:support` (line 292) | Hahn--Neumann support lemma |
| Lemma | `finite:lem:operator` (line 320) | Support-controlled operator inversion |
| Proposition | `finite:prop:evaluation` (line 364) | Evaluation is a homomorphism |
| Lemma | `finite:lem:shifted` (line 380) | Shifted division and finite Taylor remainder |
| Lemma | `finite:lem:autosupport` (line 415) | Automatic common support |
| Theorem | `finite:thm:hartogs` (line 429) | Automatic Hahn--Hartogs coherence |
| Corollary | `finite:cor:hole` (line 449) | Coherent Hartogs removal |
| Lemma | `finite:lem:ordinarydivision` (line 486) | Uniform ordinary division operators |
| Theorem | `finite:thm:matrixdivision` (line 509) | Support-controlled matrix division |
| Theorem | `finite:thm:parameterprep` (line 541) | Fixed-domain Hahn preparation with holomorphic parameters |
| Corollary | `finite:cor:oneshrink` (line 570) | One shrink, and no more |
| Theorem | `finite:thm:hpl` (line 613) | Hahn contraction formula |
| Proposition | `finite:prop:ordinarykoszul` (line 681) | The ordinary quotient and its Koszul resolution |
| Theorem | `finite:thm:finitefree` (line 703) | Uniform finite-flat zero algebra; division with the $S+M$ certificate |
| Corollary | `finite:cor:koszul` (line 748) | All Koszul relations lift, with an explicit preimage |
| Corollary | `finite:cor:restriction` (line 771) | No loss of support under restriction |
| Theorem | `finite:thm:family` (line 802) | Perturbed monomial complete intersections, with holomorphic parameters |
| Theorem | `finite:thm:finitefree15` (line 856) | Finite-free complete intersections by matrix induction |
| Lemma | `finite:lem:coordpoly` (line 888) | Coordinate characteristic polynomials |
| Lemma | `finite:lem:matrix` (line 897) | Summable matrix functional calculus |
| Theorem | `finite:thm:characters` (line 910) | All characters are evaluations |
| Theorem | `finite:thm:length` (line 940) | Local algebra comparison and exact conservation |
| Corollary | `finite:cor:rouche` (line 964) | Conservation of multiplicity; a monad form of Rouch\'e |
| Corollary | `finite:cor:monadmap` (line 971) | Finite mapping of an entire monad |
| Lemma | `finite:lem:translation` (line 1013) | Evaluation, translation, division by coordinates |
| Theorem | `finite:thm:formaldivision` (line 1022) | Uniform-support division and conservation of colength over $\Af_{n,\Gamma}$ |
| Theorem | `finite:thm:localization` (line 1036) | Uniform valuation localization of the zeros |
| Theorem | `finite:thm:fibres` (line 1056) | Finite infinitesimal fibres |
| Corollary | `finite:cor:inverse` (line 1070) | A bijection of the whole monad, with fine-analytic inverse |
| Theorem | `finite:thm:monadcount` (line 1084) | Coherent conservation of isolated intersections |
| Theorem | `finite:thm:spectral` (line 1103) | Characteristic polynomials, traces and norms |
| Proposition | `finite:prop:separation` (line 1123) | A bounded list of separating linear forms |
| Proposition | `finite:prop:resdescend` (line 1176) | The residue descends to the finite algebra |
| Corollary | `finite:cor:coefficientresidue` (line 1187) | Explicit coefficient extraction for coordinate-power leading systems |
| Theorem | `finite:thm:duality` (line 1207) | Perfect integral residue duality |
| Corollary | `finite:cor:residuereconstruction` (line 1223) | Contour recovery of the finite algebra |
| Corollary | `finite:cor:relative` (line 1238) | Relative residue duality over a parameter domain |
| Lemma | `finite:lem:witness` (line 1268) | Finite-witness transfer |
| Lemma | `finite:lem:finitedependence` (line 1288) | The ordinary finite-parameter comparison |
| Theorem | `finite:thm:trace` (line 1300) | Trace--Jacobian identity and simple-zero residues |
| Theorem | `finite:thm:bezout` (line 1342) | Residue reproducing kernel |
| Theorem | `finite:thm:localres` (line 1386) | Moving-intersection residue theorem |
| Corollary | `finite:cor:transformation` (line 1406) | Change of generators |
| Theorem | `finite:thm:transform` (line 1415) | Coordinate change by an infinitesimal displacement |
| Theorem | `finite:thm:discriminant` (line 1435) | Discriminant--Jacobian identity and the reducedness criterion |
| Proposition | `finite:prop:univtrace` (line 1464) | One-variable trace and residue formulas, stable across collisions |
| Theorem | `finite:thm:monodromy` (line 1485) | Support-preserving lift of the ordinary root cover |
| Theorem | `finite:thm:precision` (line 1512) | Precision of normal forms, residues and spectral invariants |
| Corollary | `finite:cor:discstable` (line 1542) | A discriminant threshold that preserves simple zeros |
| Theorem | `finite:thm:rootstability` (line 1559) | Sharp conditioned root stability |
| Corollary | `finite:cor:matching` (line 1610) | Stable matching of an entire simple cluster |
| Proposition | `finite:prop:sharpness` (line 1619) | Both bounds attained, and the threshold strict |

### global-divisors

Source: [surcomplex/global-divisors/article.tex](surcomplex/global-divisors/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `global:lem:support` (line 227) | Support calculus |
| Proposition | `global:prop:evaluation` (line 275) | Evaluation and identity |
| Proposition | `global:prop:sheaf` (line 292) | Support-preserving sheaf property |
| Proposition | `global:prop:units` (line 304) | Exact unit criterion |
| Proposition | `global:prop:explog` (line 320) | Positive-support exponential and logarithm |
| Lemma | `global:lem:scalarML` (line 350) | Scalar Weierstrass and Mittag--Leffler |
| Lemma | `global:lem:hermite` (line 366) | Discrete Hermite interpolation |
| Lemma | `global:lem:scalarCousin` (line 387) | Scalar additive Cousin theorem on $\C$ |
| Theorem | `global:thm:preparation` (line 425) | Uniform-support local preparation |
| Corollary | `global:cor:roots` (line 458) | All roots in a monad |
| Lemma | `global:lem:division` (line 474) | Deformed division |
| Lemma | `global:lem:polefree` (line 498) | Pole-free fractions |
| Theorem | `global:thm:PID` (line 512) | Principal-ideal-domain stalks |
| Proposition | `global:prop:nonlocal` (line 534) | Non-locality, and the integral model |
| Corollary | `global:cor:Picmeaning` (line 548) | Meaning of the Picard group here |
| Theorem | `global:thm:ML` (line 592) | Uniform-support Mittag--Leffler criterion |
| Corollary | `global:cor:interp` (line 618) | Entire interpolation with an exact support criterion |
| Theorem | `global:thm:divisor` (line 638) | Sharp global moving-divisor criterion |
| Proposition | `global:prop:realizationtorsor` (line 692) | The freedom in realization |
| Corollary | `global:cor:splitting` (line 762) | Failure of arbitrary global divisor splitting |
| Proposition | `global:prop:restrictedalgebra` (line 796) | Restricted product algebra |
| Theorem | `global:thm:interpolation` (line 812) | Deformed Hermite interpolation |
| Corollary | `global:cor:CRT` (line 835) | Chinese remainder quotient |
| Theorem | `global:thm:MLmoving` (line 876) | Sharp moving-pole Mittag--Leffler theorem |
| Theorem | `global:thm:aut` (line 913) | Global inverse for positive-support perturbations |
| Corollary | `global:cor:motion` (line 937) | Exact interpolation of simple motions |
| Theorem | `global:thm:cousincriterion` (line 975) | Necessary and sufficient Cousin criterion |
| Theorem | `global:thm:obstruction` (line 1013) | A concrete obstruction subspace |
| Corollary | `global:cor:H1injection` (line 1040) | First cohomology detected by descending scales |
| Corollary | `global:cor:H1size` (line 1058) | Size and local invisibility |
| Proposition | `global:prop:divPic` (line 1085) | The divisor and logarithmic obstructions coincide |
| Proposition | `global:prop:Picreduction` (line 1099) | Reduction of the Picard group to positive supports |
| Lemma | `global:lem:descending` (line 1122) | Descending positive sequences |
| Theorem | `global:thm:dichotomy` (line 1130) | Picard-group vanishing dichotomy |
| Theorem | `global:thm:dimension` (line 1159) | Continuum many independent classes, and the exact dimension |
| Proposition | `global:prop:fullH1` (line 1184) | The full additive sheaf is already obstructed in cyclic rank |
| Proposition | `global:prop:Cartierexample` (line 1208) | An effective divisor with trivial ordinary reduction but no global equation |

### nonabelian-support

Source: [surcomplex/nonabelian-support/article.tex](surcomplex/nonabelian-support/article.tex).

All statements in this newly indexed report remain **pending**. Criterion P
uses normalized polar-factor support, whereas Criterion M uses raw monodromy
support; the two predicates must not be identified.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `nab:lem:neumann` (line 561) | Neumann support calculus; classical input |
| Lemma | `nab:lem:inverse` (line 597) | Positive inversion and formal functions |
| Lemma | `nab:lem:finiteclosure` (line 628) | Finite decomposition inside the generated monoid |
| Lemma | `nab:lem:laurent` (line 669) | The ordinary splitting algebras |
| Lemma | `nab:lem:mlplane` (line 693) | Isolated singular parts on the plane |
| Lemma | `nab:lem:mlsurface` (line 718) | Open-surface version |
| Lemma | `nab:lem:free` (line 745) | Free based meridians |
| Lemma | `nab:lem:period` (line 780) | A linear period right inverse |
| Theorem | `nab:thm:local` (line 840) | Local normalized factorization |
| Proposition | `nab:prop:rightgauge` (line 876) | Right-gauge invariance |
| Corollary | `nab:cor:unitriangular` (line 891) | Unitriangular factors |
| Theorem | `nab:thm:frobenius` (line 941) | A common-disk positive Frobenius factorization |
| Theorem | `nab:thm:criterion` (line 1025) | Exact nonabelian Cousin criterion: Criterion P |
| Proposition | `nab:prop:torsor` (line 1111) | Right torsor of splittings |
| Corollary | `nab:cor:localgauges` (line 1135) | Removal of arbitrarily supported regular data |
| Corollary | `nab:cor:coordinates` (line 1150) | Coordinate independence of admissibility |
| Corollary | `nab:cor:extension` (line 1168) | Absoluteness under ordered extension |
| Proposition | `nab:prop:rankone` (line 1189) | Recovery of the rank-one singular-support test |
| Proposition | `nab:prop:heisenberg` (line 1230) | Closed Heisenberg factorization |
| Theorem | `nab:thm:hidden` (line 1280) | Hidden rank-three obstruction |
| Proposition | `nab:prop:logdiag` (line 1352) | Logarithm diagnostic |
| Lemma | `nab:lem:chain` (line 1384) | Chain identity |
| Theorem | `nab:thm:depth` (line 1432) | Arbitrarily deep central support obstructions |
| Proposition | `nab:prop:integraltrivial` (line 1507) | For triviality, the reduced framing costs nothing |
| Corollary | `nab:cor:nontrivialbundles` (line 1527) | Nontrivial determinant-one integral bundles |
| Corollary | `nab:cor:bounded` (line 1543) | Exhaustion-invisible nontriviality |
| Theorem | `nab:thm:Stein` (line 1608) | Support-controlled Stein splitting |
| Theorem | `nab:thm:deformation` (line 1651) | Support-controlled deformation rigidity |
| Lemma | `nab:lem:groups` (line 1687) | Ordered-group alternative |
| Theorem | `nab:thm:dichotomy` (line 1703) | Universal positive rigidity and its failure |
| Theorem | `nab:thm:fundamental` (line 1838) | Fundamental matrix with a support certificate |
| Lemma | `nab:lem:triangular` (line 1913) | Triangular change of monodromy |
| Theorem | `nab:thm:RH` (line 1955) | Support-sensitive Riemann--Hilbert realization: Criterion M |
| Proposition | `nab:prop:intrinsic` (line 2049) | Independence of the meridian basis |
| Proposition | `nab:prop:conjugation` (line 2074) | Fixed conjugation and enlargement cannot repair support |
| Theorem | `nab:thm:gauge` (line 2111) | Framed classification with controlled support |
| Theorem | `nab:thm:entiregauge` (line 2147) | Entire extension of a logarithmic comparison gauge |
| Corollary | `nab:cor:slice` (line 2180) | A global normal slice for logarithmic connections |
| Corollary | `nab:cor:finite` (line 2207) | Unique positive residue matrices for finite data |
| Lemma | `nab:lem:det` (line 2238) | Determinants and positive connections |
| Theorem | `nab:thm:SL` (line 2253) | Traceless normalized realization |
| Proposition | `nab:prop:mixed` (line 2408) | The first nonabelian correction |
| Proposition | `nab:prop:dependence` (line 2533) | Finite exponent dependence |
| Proposition | `nab:prop:basechange` (line 2567) | Compatibility with enlargement of the workspace |
| Proposition | `nab:prop:discontinuous` (line 2597) | No continuous linear period right inverse |

### polynomial-algebra

Source: [surcomplex/polynomial-algebra/article.tex](surcomplex/polynomial-algebra/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `polynomial:prop:workspace` (line 376) | A workspace for every set of data |
| Lemma | `polynomial:lem:support` (line 475) | Hahn--Neumann support calculus |
| Theorem | `polynomial:thm:fta` (line 586) | Finite polynomial algebra over $K$ |
| Theorem | `polynomial:thm:crt` (line 647) | Finite Hermite interpolation and CRT |
| Proposition | `polynomial:prop:rootbounds` (line 725) | Cauchy bounds and a radial bound |
| Theorem | `polynomial:thm:gausslucas` (line 762) | Surcomplex Gauss--Lucas |
| Proposition | `polynomial:prop:weighted` (line 791) | Weighted incomplete polynomials, and a converse |
| Theorem | `polynomial:thm:jensen` (line 817) | Surcomplex Jensen disk theorem |
| Lemma | `polynomial:lem:compression` (line 861) | Differentiating compression |
| Lemma | `polynomial:lem:schur` (line 872) | Finite-dimensional Schur inequality |
| Theorem | `polynomial:thm:schoenberg` (line 891) | Sharp surcomplex Schoenberg inequality |
| Theorem | `polynomial:thm:orderrouche` (line 966) | Rouch\'e on an order-modulus circle |
| Corollary | `polynomial:cor:pellet` (line 996) | Monomial dominance |
| Theorem | `polynomial:thm:hermite` (line 1047) | Hermite's signature criterion over surreal real closed fields |
| Theorem | `polynomial:thm:pseudozeros` (line 1105) | Exact uncertainty root sets in two geometries |
| Lemma | `polynomial:lem:gaussvaluation` (line 1193) | Multiplicativity |
| Theorem | `polynomial:thm:initialroots` (line 1216) | Initial polynomial and all residue-direction root counts |
| Corollary | `polynomial:cor:valrouche` (line 1272) | Valuation Rouch\'e: preservation of the whole initial polynomial |
| Theorem | `polynomial:thm:newton` (line 1317) | Newton's root-valuation rule |
| Theorem | `polynomial:thm:imageballs` (line 1419) | Exact image and fiber degree |
| Corollary | `polynomial:cor:normalization` (line 1461) | Affine normalization of a finite polynomial problem |
| Theorem | `polynomial:thm:finitemap` (line 1491) | A polynomial is a finite flat map of its degree |
| Theorem | `polynomial:thm:branchvalues` (line 1515) | Branch-value polynomial |
| Proposition | `polynomial:prop:ramification` (line 1543) | Finite and infinite ramification |
| Corollary | `polynomial:cor:polynomialmaps` (line 1564) | Surjectivity and polynomial injections |
| Lemma | `polynomial:lem:initialderivative` (line 1584) | The derivative of an initial polynomial |
| Theorem | `polynomial:thm:criticalballs` (line 1607) | Exact critical-point conservation in occupied balls |
| Corollary | `polynomial:cor:ramificationball` (line 1639) | Ramification count on an arbitrary mapping ball |
| Corollary | `polynomial:cor:nearest` (line 1660) | Valuative Gauss--Lucas and nearest neighbours |
| Theorem | `polynomial:thm:branch` (line 1686) | Critical residue directions inside a cluster |
| Corollary | `polynomial:cor:tree` (line 1748) | Critical allocation by the root tree |
| Proposition | `polynomial:prop:clusterdisc` (line 1815) | Discriminant as a finite level sum |
| Proposition | `polynomial:prop:disctree` (line 1837) | Discriminant as a sum over the root tree |
| Theorem | `polynomial:thm:hensel` (line 1889) | Support-controlled coprime Hensel factorization |
| Corollary | `polynomial:cor:simpleroot` (line 1942) | Simple-root lifting and the first correction |
| Corollary | `polynomial:cor:clusterfactor` (line 1961) | Canonical standard-part cluster factors |
| Theorem | `polynomial:thm:parameterhensel` (line 1999) | Parameter factor lifting without repeated shrinking |
| Theorem | `polynomial:thm:holder` (line 2081) | Optimal valuation-H\"older root matching |
| Corollary | `polynomial:cor:derivativeholder` (line 2132) | Simultaneous stability for derivatives |
| Theorem | `polynomial:thm:stability` (line 2182) | Exact matching, full cluster stability, and a second-order Newton error |
| Corollary | `polynomial:cor:discprecision` (line 2309) | Discriminant precision protects all clusters |
| Corollary | `polynomial:cor:treestability` (line 2388) | Preservation of the tree and of its critical directions |
| Theorem | `polynomial:thm:residuepairing` (line 2464) | Universal residue pairing and explicit dual basis |
| Theorem | `polynomial:thm:trace` (line 2524) | Universal trace identity |
| Proposition | `polynomial:prop:localresidues` (line 2595) | Finite residue formula at multiple roots |
| Proposition | `polynomial:prop:tracenormroots` (line 2636) | Field-level traces and norms, including collisions |
| Theorem | `polynomial:thm:discriminant` (line 2661) | Discriminant and trace-pairing degeneration |
| Lemma | `polynomial:lem:zariski` (line 2747) | Zariski's lemma in the needed form |
| Theorem | `polynomial:thm:nullstellensatz` (line 2775) | Surcomplex Nullstellensatz |
| Proposition | `polynomial:prop:finitealgebra` (line 2837) | Finite fibers and local lengths |
| Theorem | `polynomial:thm:globalfree` (line 2926) | Global finite-free normal forms |
| Corollary | `polynomial:cor:globalbezout` (line 2978) | A global B\'ezout count, including infinite-scale roots |
| Theorem | `polynomial:thm:multiperfect` (line 3037) | A coefficient-independent perfect pairing |
| Theorem | `polynomial:thm:jacobian` (line 3078) | B\'ezoutian kernel and Jacobian duality |
| Corollary | `polynomial:cor:eulerjacobi` (line 3133) | Simple-root weights and Euler--Jacobi vanishing |
| Theorem | `polynomial:thm:polyparameters` (line 3177) | Global polynomial families on one ordinary parameter domain |
| Theorem | `polynomial:thm:analyticcomparison` (line 3219) | Polynomial identification of the Jacobian trace element |

### rank-one-berkovich

Source: [surcomplex/rank-one-berkovich/article.tex](surcomplex/rank-one-berkovich/article.tex).

All statements in this newly indexed report remain **pending**.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `prop:spherical` (line 266) | Untitled |
| Proposition | `prop:topologies` (line 312) | Untitled |
| Theorem | `thm:series` (line 340) | Untitled |
| Proposition | `prop:rankobstruction` (line 375) | Untitled |
| Proposition | `prop:banach` (line 439) | Untitled |
| Proposition | `prop:supnorm` (line 461) | Untitled |
| Theorem | `thm:chain` (line 529) | Untitled |
| Corollary | `cor:rescale` (line 609) | Untitled |
| Lemma | `lem:polydivision` (line 652) | Untitled |
| Theorem | `thm:preparation` (line 672) | One-variable Weierstrass division and preparation |
| Corollary | `cor:units` (line 722) | Untitled |
| Corollary | `cor:finitequotient` (line 738) | Untitled |
| Theorem | `thm:rootcounts` (line 794) | Untitled |
| Corollary | `cor:rouche` (line 825) | Valuation Rouch\'e theorem |
| Lemma | `lem:hensel` (line 841) | Unit-derivative Hensel lifting |
| Proposition | `prop:compact` (line 879) | Untitled |
| Corollary | `cor:types` (line 920) | Untitled |
| Proposition | `prop:slopes` (line 1027) | Untitled |
| Theorem | `thm:jensen` (line 1063) | Valuation Jensen formula |
| Proposition | `prop:primitive` (line 1099) | Untitled |
| Proposition | `prop:ode` (line 1139) | Untitled |
| Theorem | `thm:annulusderham` (line 1206) | Untitled |
| Proposition | `prop:residuepullback` (line 1235) | Untitled |
| Proposition | `prop:annuluscontract` (line 1269) | Untitled |
| Theorem | `thm:liouville` (line 1372) | Growth and zero-free rigidity |
| Theorem | `thm:canonicalproduct` (line 1400) | Untitled |
| Theorem | `thm:thetazeros` (line 1519) | All zeros and their first terms |
| Corollary | `cor:thetaresidue` (line 1606) | Untitled |

### spectral-theory

Source: [surcomplex/spectral-theory/article.tex](surcomplex/spectral-theory/article.tex).

All statements in this newly indexed report remain **pending**.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `prop:localization` (line 275) | Finite-data localization |
| Lemma | `lem:CS` (line 322) | Cauchy--Schwarz and orthogonal decomposition |
| Theorem | `thm:spectral` (line 372) | Hermitian spectral theorem |
| Proposition | `prop:normal` (line 395) | Schur form and normal matrices |
| Proposition | `prop:positive` (line 431) | Positive square root and inertia |
| Theorem | `thm:svd` (line 464) | Singular value decomposition |
| Theorem | `thm:minmax` (line 554) | Variational principles |
| Theorem | `thm:weyl` (line 608) | Ordered Lipschitz bounds |
| Theorem | `thm:HW` (line 628) | A Frobenius eigenvalue bound |
| Theorem | `thm:leastsquares` (line 680) | Least squares with an attained minimum |
| Theorem | `thm:EY` (line 713) | Eckart--Young bounds over $F$ |
| Lemma | `lem:valnorm` (line 766) | Valuation of a Euclidean norm |
| Lemma | `lem:unitaryintegral` (line 790) | Unitary matrices preserve the integral lattice |
| Lemma | `lem:DeltaInvariant` (line 823) | Integral row and column invariance |
| Theorem | `thm:scales` (line 837) | Singular scales are determinantal scales |
| Theorem | `thm:gram` (line 912) | Positive Cauchy--Binet identity |
| Theorem | `thm:residual` (line 964) | Residual polynomial for a singular-scale block |
| Corollary | `cor:stRank` (line 1017) | Rank after reduction |
| Theorem | `thm:filtration` (line 1050) | Filtration dimensions |
| Proposition | `prop:elimination` (line 1108) | Exact scale elimination |
| Theorem | `thm:distance` (line 1188) | Distance to singularity |
| Theorem | `thm:inversepert` (line 1222) | Inverse and linear-system perturbation |
| Theorem | `thm:precision` (line 1265) | Preserving visible singular data |
| Proposition | `prop:pseudo` (line 1321) | Exact perturbation interpretation |
| Theorem | `thm:subspace` (line 1374) | A separated-subspace bound |
| Corollary | `cor:clustergap` (line 1420) | Using an unperturbed cluster gap |
| Proposition | `prop:effective` (line 1488) | Exact effective matrix |
| Theorem | `thm:series` (line 1613) | Matrix inverse and square-root series |
| Proposition | Line 1714 (unlabeled) | Ordinary data and infinitesimal regularization |

### trigonometry

Source: [surcomplex/trigonometry/article.tex](surcomplex/trigonometry/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `trigonometry:lem:support` (line 349) | Hahn--Neumann support calculus |
| Proposition | `trigonometry:prop:topology` (line 399) | Degeneracy of fine convergence |
| Proposition | `trigonometry:prop:lift` (line 431) | Local calculus and one-variable sign lifting |
| Lemma | `trigonometry:lem:leading` (line 460) | Leading-term test for a lifted germ |
| Theorem | `trigonometry:thm:identities` (line 500) | Elementary trigonometry on finite surreal angles |
| Proposition | `trigonometry:prop:order` (line 540) | Signs and monotonicity |
| Proposition | `trigonometry:prop:leading` (line 565) | Exact infinitesimal leading orders |
| Proposition | `trigonometry:prop:normalization` (line 588) | Normalization of the finite trigonometric pair |
| Proposition | `trigonometry:prop:rotation` (line 638) | Algebraic angle addition and rotations |
| Theorem | `trigonometry:thm:polar` (line 664) | Polar decomposition and the angle group |
| Corollary | `trigonometry:cor:representatives` (line 697) | Representatives, roots, and torsion |
| Theorem | `trigonometry:thm:cayley` (line 743) | Projective half-angle parametrization of every surreal direction |
| Theorem | `trigonometry:thm:inverse` (line 782) | Inverse tangent, sine, and cosine |
| Proposition | `trigonometry:prop:acosendpoint` (line 852) | Endpoint ramification of inverse cosine |
| Theorem | `trigonometry:thm:metric` (line 880) | Angular and chordal comparison |
| Corollary | `trigonometry:cor:phaseisometry` (line 912) | Local valuation isometry of phase and rotation displacement |
| Corollary | `trigonometry:cor:directionstability` (line 936) | Stability of direction under a relative perturbation |
| Theorem | `trigonometry:thm:anglesum` (line 969) | Euclidean angle sum over the surreal field |
| Theorem | `trigonometry:thm:trianglelaws` (line 991) | Triangle laws |
| Corollary | `trigonometry:cor:right` (line 1019) | Right triangles and the full range of slopes |
| Theorem | `trigonometry:thm:sss` (line 1030) | Existence, congruence, and similarity |
| Theorem | `trigonometry:thm:heron` (line 1079) | Heron, half-angle, incircle and bisector formulas |
| Theorem | `trigonometry:thm:euler` (line 1118) | Euler's incentre--circumcentre identity |
| Corollary | `trigonometry:cor:areabound` (line 1140) | A scale-independent area inequality |
| Theorem | `trigonometry:thm:cevian` (line 1155) | Sine ratios for a cevian |
| Theorem | `trigonometry:thm:ceva` (line 1172) | Trigonometric Ceva |
| Proposition | `trigonometry:prop:inscribed` (line 1211) | Inscribed-angle theorem |
| Theorem | `trigonometry:thm:ptolemy` (line 1224) | Ptolemy inequality and its cyclic equality case |
| Corollary | `trigonometry:cor:polygon` (line 1253) | Finite regular polygons at surreal scale |
| Theorem | `trigonometry:thm:valuationtriangle` (line 1299) | Valuation form of the triangle laws |
| Theorem | `trigonometry:thm:defect` (line 1338) | A quadratic defect formula |
| Theorem | `trigonometry:thm:flat` (line 1370) | Quadratic slack and reciprocal circumradius in normalized coordinates |
| Theorem | `trigonometry:thm:flatrelative` (line 1408) | Exact gap identity and the relative flatness threshold |
| Theorem | `trigonometry:thm:amplitude` (line 1545) | Amplitude--phase reduction and intersection count |
| Theorem | `trigonometry:thm:tangency` (line 1581) | Tangency, angular splitting, and loss of valuation |
| Theorem | `trigonometry:thm:fold` (line 1623) | The cosine fold |
| Theorem | `trigonometry:thm:residuepairing` (line 1665) | A collision-stable residue pairing |
| Lemma | `trigonometry:lem:hensel` (line 1763) | A simple residue root of a polynomial |
| Theorem | `trigonometry:thm:stability` (line 1782) | Sharp angular root-stability bound |
| Proposition | `trigonometry:prop:sharp` (line 1837) | The threshold and both exponents are sharp |
| Theorem | `trigonometry:thm:conditioned` (line 1861) | Conditioned inversion of cosine |
| Theorem | `trigonometry:thm:stripexp` (line 1946) | Canonical strip exponential |
| Theorem | `trigonometry:thm:striptrig` (line 1977) | Complex-variable identities and zero sets |
| Theorem | `trigonometry:thm:sinefibers` (line 2004) | Surjectivity and complete fibres of strip sine |
| Corollary | `trigonometry:cor:sineinverse` (line 2029) | Explicit inverse branches |
| Theorem | `trigonometry:thm:polyroots` (line 2066) | Algebraization and the $2n$ root bound |
| Corollary | `trigonometry:cor:chebyshev` (line 2098) | Chebyshev and extremum equations |
| Theorem | `trigonometry:thm:cluster` (line 2128) | Exact cluster multiplicity and coefficient support |
| Theorem | `trigonometry:thm:fourier` (line 2205) | Finite Fourier inversion, sampling, and Parseval |
| Theorem | `trigonometry:thm:parseval` (line 2263) | Finite Fourier identities over $\SC$ |
| Lemma | `trigonometry:lem:twosquares` (line 2319) | Nonnegative polynomials over a real closed field |
| Theorem | `trigonometry:thm:fejer` (line 2333) | Surcomplex Fej\'er--Riesz theorem |
| Corollary | `trigonometry:cor:coeffbounds` (line 2395) | Fourier coefficient bounds from positivity |
| Theorem | `trigonometry:thm:spherical` (line 2463) | Spherical cosine and sine laws |
| Proposition | `trigonometry:prop:diskmetric` (line 2515) | Disk invariance and metric properties |
| Theorem | `trigonometry:thm:hyperbolic` (line 2545) | Hyperbolic triangle laws over $\No$ |
| Theorem | `trigonometry:thm:arcs` (line 2607) | Circle length and sector area at every radius |
| Proposition | `trigonometry:prop:perimeters` (line 2634) | Failure of fine convergence of inscribed perimeters |
| Theorem | `trigonometry:thm:globalexp` (line 2711) | Canonical global exponential and its period class |
| Corollary | `trigonometry:cor:globalzeros` (line 2750) | Zero classes and periods |
| Theorem | `trigonometry:thm:characters` (line 2771) | All extensions of the finite phase |
| Theorem | `trigonometry:thm:infiniteperiods` (line 2819) | Infinite periods are unavoidable |
| Theorem | `trigonometry:thm:infinitefrequency` (line 2854) | No coherent infinite-frequency bounded sine |
| Theorem | `trigonometry:thm:allscale` (line 2879) | Why all-scale coherence forces a polynomial |

### surquaternions

Source: [surquaternions/surquaternions/article.tex](surquaternions/surquaternions/article.tex).

All statements in this newly indexed report remain **pending**. Quaternion
multiplication, conjugation and leading coefficients retain their stated
noncommutative order; scalar commutative proofs do not transfer implicitly.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `squat:thm:localization` (line 330) | Set localization |
| Proposition | `squat:prop:assoc` (line 562) | Associativity and change of scalars |
| Theorem | `squat:thm:division` (line 576) | Hamilton algebra over an ordered field |
| Proposition | `squat:prop:center` (line 601) | Center, commutators, and the absence of a ring order |
| Proposition | `squat:prop:norm` (line 624) | Euclidean identities without completeness |
| Theorem | `squat:thm:conjugacy` (line 683) | Slice decomposition, centralizers, conjugacy |
| Proposition | `squat:prop:sqrt` (line 713) | Explicit square roots |
| Proposition | `squat:prop:matrix` (line 741) | Matrix realization |
| Theorem | `squat:thm:rotations` (line 780) | Rotations, spin, and inner automorphisms |
| Proposition | `squat:prop:charts` (line 844) | Two rational charts on the unit group |
| Lemma | `squat:lem:twisted` (line 921) | Twisted product and left division |
| Lemma | `squat:lem:sphere-remainder` (line 959) | Remainder on a sphere |
| Theorem | `squat:thm:polynomialzeros` (line 995) | Complete zero-class criterion |
| Theorem | `squat:thm:fta` (line 1009) | Constructive fundamental theorem and factorization |
| Proposition | `squat:prop:rootcount` (line 1038) | Conservation of class multiplicity |
| Theorem | `squat:thm:normal` (line 1096) | Normal form, multiplication, localization |
| Theorem | `squat:thm:valuation` (line 1143) | Exact valuation, leading coefficients, and residue |
| Proposition | `squat:prop:neumann` (line 1200) | Exact geometric inverse and error certificate |
| Lemma | `squat:lem:neumann` (line 1248) | Positive-support (Neumann) lemma, all lengths |
| Theorem | `squat:thm:discrete` (line 1299) | Set discreteness and the failure of sequential completion |
| Theorem | `squat:thm:principal-log` (line 1370) | Local exponential--logarithm equivalence |
| Proposition | `squat:prop:bch` (line 1407) | Baker--Campbell--Hausdorff at positive valuation |
| Proposition | `squat:prop:adjoint` (line 1462) | Adjoint series at infinite arguments |
| Theorem | `squat:thm:rotation-log` (line 1479) | Logarithms of infinitesimal rotations |
| Theorem | `squat:thm:graded` (line 1494) | Associated graded rotation algebra |
| Proposition | `squat:prop:finiteangles` (line 1537) | Every direction has a finite angle; the finite phase theorem |
| Theorem | `squat:thm:polar` (line 1560) | Polar representation at arbitrary surreal radius |
| Theorem | `squat:thm:polarlog` (line 1611) | Polar logarithms and arbitrary-scale roots |
| Theorem | `squat:thm:globalexp` (line 1708) | Properties of the global radial exponential |
| Theorem | `squat:thm:logfibres` (line 1750) | Complete logarithm fibres |
| Theorem | `squat:thm:exp-derivative` (line 1814) | Radial derivative and critical spheres at infinite radius |
| Theorem | `squat:thm:derivations` (line 1883) | Derivation decomposition |
| Corollary | `squat:cor:bmconstants` (line 1951) | Constants, surjectivity, antiderivatives |
| Proposition | `squat:prop:angular` (line 1979) | Angular velocity identity |
| Lemma | `squat:lem:small` (line 2000) | Finite inputs have infinitesimal derivatives |
| Theorem | `squat:thm:nooscillation` (line 2009) | No constant-frequency quaternionic oscillation |
| Corollary | `squat:cor:nochain` (line 2030) | No global commuting chain rule |
| Theorem | `squat:thm:spectral` (line 2111) | Hermitian spectral theorem over $\HF$ |
| Theorem | `squat:thm:projector` (line 2203) | Spectral-projector estimate at arbitrary surreal gap scale |
| Proposition | `squat:prop:evaluation` (line 2320) | Uniform-support evaluation |
| Proposition | `squat:prop:representation` (line 2367) | Slice representation, Cauchy--Riemann, twisted product |
| Theorem | `squat:thm:representation` (line 2457) | Representation formula and coherent identity principle |
| Theorem | `squat:thm:cauchy-general` (line 2528) | Common-domain Cauchy formula at arbitrary slice direction |
| Theorem | `squat:thm:cauchy-slice` (line 2572) | Coefficientwise Cauchy formula on a fixed slice |
| Theorem | `squat:thm:fueter` (line 2641) | Fueter transfer: polynomials and coherent families |
| Theorem | `squat:thm:lifting` (line 2713) | Support-controlled implicit lifting |
| Proposition | `squat:prop:sylvester` (line 2780) | Square-root linearization and condition numbers |
| Theorem | `squat:thm:conditioned` (line 2833) | A sufficient conditioned square-root threshold |

### broadcast-sum-of-surreal-sequences

Source: [surreal/broadcast-sum-of-surreal-sequences/article.tex](surreal/broadcast-sum-of-surreal-sequences/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:rank-monotone` (line 341) | Monotonicity of the auxiliary rank |
| Theorem | `thm:rank` (line 359) | Well-foundedness and a birthday bound |
| Lemma | `lem:commute` (line 407) | Commutation |
| Lemma | `lem:legalize` (line 425) | A nonidentity action can be legalized |
| Lemma | `lem:survive` (line 441) | The earlier witness survives |
| Theorem | `thm:number` (line 455) | Every broadcast game is a number |
| Proposition | `prop:basic` (line 502) | Relabelling, zeros, and negation |
| Theorem | `thm:finite-support` (line 519) | Finite-support agreement |
| Corollary | `cor:ordinal` (line 541) | Ordinal extension |
| Theorem | `thm:perturbation` (line 566) | Finite-short-perturbation bound |
| Corollary | `cor:cofinite` (line 624) | Untitled |
| Lemma | `lem:X-cuts` (line 645) | Untitled |
| Theorem | `thm:constants` (line 672) | Constant dyadic values and finite defects |
| Corollary | `cor:dyadic-tail` (line 729) | Cofinite dyadic leading scale |
| Lemma | `lem:left-family` (line 759) | Left options |
| Lemma | `lem:right-family` (line 786) | Right options |
| Theorem | `thm:finite-E` (line 808) | Untitled |
| Theorem | `thm:infinite-E` (line 827) | Untitled |
| Lemma | `lem:pure-power` (line 872) | Pure geometric tails |
| Corollary | `cor:nonmonotone` (line 886) | Failure of weak monotonicity |
| Corollary | `cor:scaling` (line 906) | Failure of finite-scaling compatibility |

### canonical-forms-need-not-be-subgraphs

Source: [surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex](surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:pentagon` (line 452) | A pentagon represents $1/2$ |
| Theorem | `thm:second-pentagon` (line 527) | A second pentagon of value $1/2$ |
| Lemma | Line 641 (unlabeled) | Convexity of a simplicity cone |
| Lemma | Line 659 (unlabeled) | Descent toward a prefix |
| Theorem | `thm:prefix-occurrence` (line 682) | Prefix occurrence |
| Lemma | Line 716 (unlabeled) | The finite canonical prefix chain |
| Theorem | `thm:prefix-path` (line 769) | A path through every finite prefix |
| Lemma | Line 802 (unlabeled) | One-sided finite cuts have integer values |
| Theorem | `thm:minima` (line 816) | Exact graph minima |
| Corollary | Line 861 (unlabeled) | Untitled |
| Lemma | Line 877 (unlabeled) | Forest obstruction |
| Theorem | `thm:minimal-forms` (line 904) | The vertex-minimal forms |
| Corollary | Line 960 (unlabeled) | Unique edge-minimizer |
| Lemma | Line 1005 (unlabeled) | Triangle-free forms on at most four vertices |
| Theorem | `thm:smallest` (line 1041) | Smallest size and rank of a counterexample |
| Proposition | Line 1085 (unlabeled) | A rank-minimal non-containing form |
| Lemma | Line 1179 (unlabeled) | Untitled |
| Theorem | `thm:odd-cycle` (line 1196) | Odd-cycle family |
| Lemma | Line 1245 (unlabeled) | Untitled |
| Theorem | `thm:odd-cycle-two` (line 1259) | Second odd-cycle family |
| Theorem | `thm:even-cycle` (line 1302) | Even-cycle family |
| Proposition | Line 1333 (unlabeled) | All cycle lengths except four |
| Theorem | `thm:extremal` (line 1352) | Exact extremal function for $1/2$ |
| Theorem | `thm:high-girth` (line 1425) | Spaced-spine construction |
| Corollary | Line 1495 (unlabeled) | Unbounded girth at every fixed value |
| Corollary | Line 1509 (unlabeled) | Avoiding every fixed cyclic graph |
| Proposition | Line 1525 (unlabeled) | A Fibonacci bound on the unfolded leaves |
| Proposition | Line 1562 (unlabeled) | A denominator-sensitive bound, second proof |
| Lemma | Line 1662 (unlabeled) | Separated integer markers |
| Lemma | Line 1710 (unlabeled) | Value preservation |
| Lemma | Line 1723 (unlabeled) | No unintended identifications |
| Lemma | Line 1752 (unlabeled) | Graph bounds |
| Theorem | `thm:sparse` (line 1781) | Planar high-girth representation theorem |
| Lemma | Line 1835 (unlabeled) | A triangle in every noninteger canonical graph |
| Theorem | `thm:integer-classification` (line 1854) | Exactly the integers, unlabelled version |
| Theorem | `thm:classification-rooted` (line 1889) | Exactly the integers, rooted-colour version |
| Proposition | Line 1956 (unlabeled) | A limit-stage coherence obstruction |
| Proposition | Line 2026 (unlabeled) | Exact high-girth forms of $\omega$ |
| Proposition | Line 2065 (unlabeled) | No transfinite form has finite outdegree everywhere |

### genetic-gaps-and-primitives

Source: [surreal/genetic-gaps-and-primitives/article.tex](surreal/genetic-gaps-and-primitives/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:q` (line 223) | A bounded sign-preserving rational function |
| Lemma | `lem:binary` (line 241) | A binary cut test |
| Theorem | `thm:evaluation` (line 267) | Exact evaluation |
| Proposition | `prop:genetic` (line 327) | Untitled |
| Lemma | `lem:translation` (line 393) | Invariance under finite translation |
| Theorem | `thm:zero` (line 406) | The kernel is not just the constants |
| Theorem | `thm:primitive` (line 432) | Counterexample to genetic primitive uniqueness |
| Corollary | Line 468 (unlabeled) | Failure of normalized global uniqueness |
| Theorem | `thm:sup` (line 492) | Counterexample to the entire-genetic sup conjecture |
| Theorem | `thm:general` (line 546) | General gap-indicator construction |
| Proposition | Line 590 (unlabeled) | Cofinality is the invariant |
| Theorem | `thm:auto` (line 615) | Untitled |
| Theorem | `thm:independent` (line 659) | Ordinal-indexed finite linear independence |
| Proposition | `prop:rational` (line 769) | Rational primitives remain unique |
| Proposition | `prop:field` (line 797) | Untitled |

### gonshor-laurent-birthdays

Source: [surreal/gonshor-laurent-birthdays/article.tex](surreal/gonshor-laurent-birthdays/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:main` (line 143) | Laurent-series restriction |
| Lemma | `lem:add` (line 253) | Untitled |
| Lemma | `lem:realproduct` (line 291) | Real scalar product bound |
| Lemma | `lem:prefix` (line 332) | Prefixes and countable unions |
| Lemma | `lem:block` (line 355) | Untitled |
| Theorem | `thm:ordinalpoly` (line 388) | Ordinal-exponent polynomials |
| Theorem | `thm:finiteformula` (line 460) | Finite Laurent formula |
| Corollary | `cor:split` (line 538) | Exact finite splitting |
| Lemma | `lem:bounded` (line 579) | Untitled |
| Lemma | `lem:degree` (line 615) | Untitled |
| Lemma | `lem:crossmono` (line 637) | Positive monomial times bounded part |
| Corollary | `cor:crosspoly` (line 687) | Untitled |
| Theorem | `thm:finiteproduct` (line 704) | Finite Laurent product theorem |
| Corollary | `cor:strict` (line 733) | Equality with a finite negative tail |
| Theorem | `thm:infinite` (line 776) | Infinite Laurent birthday formula |
| Lemma | `lem:jets` (line 820) | Finite-jet stabilization |
| Corollary | `cor:reciprocal` (line 923) | Untitled |
| Corollary | `cor:spectrum` (line 957) | Untitled |

### gonshor-product-birthdays

Source: [surreal/gonshor-product-birthdays/surreal_product_birthdays.tex](surreal/gonshor-product-birthdays/surreal_product_birthdays.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | Line 254 (unlabeled) | Untitled |
| Lemma | Line 285 (unlabeled) | Untitled |
| Proposition | Line 330 (unlabeled) | Untitled |
| Theorem | Line 451 (unlabeled) | Exact birthday |
| Corollary | Line 573 (unlabeled) | Untitled |
| Theorem | Line 595 (unlabeled) | Sharp support bound |
| Proposition | Line 625 (unlabeled) | Strict degree gap |
| Lemma | Line 664 (unlabeled) | Dyadic factors |
| Lemma | Line 689 (unlabeled) | A dyadic scalar cannot increase the leading birthday data |
| Theorem | Line 740 (unlabeled) | Product birthdays on \(\A\) |
| Corollary | Line 764 (unlabeled) | Degree does not rise |
| Proposition | Line 799 (unlabeled) | No full convolution is needed |
| Proposition | Line 946 (unlabeled) | Untitled |
| Proposition | Line 975 (unlabeled) | Untitled |

### hahn-evaluation-at-omega

Source: [surreal/hahn-evaluation-at-omega/article.tex](surreal/hahn-evaluation-at-omega/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:witness` (line 311) | The formal square-root witness |
| Theorem | `thm:main` (line 347) | Negative answer to Problem 7.7 |
| Proposition | `prop:small` (line 380) | Untitled |
| Lemma | `lem:H` (line 499) | The nonnegative witness pair |
| Theorem | `thm:semiring` (line 535) | Nonnegative-coefficient obstruction |
| Lemma | `lem:unitsquare` (line 591) | Square roots of formal units |
| Lemma | `lem:unit-root` (line 612) | Square roots of units, general form |
| Theorem | `thm:necessary` (line 637) | Necessary infinitesimal condition |
| Proposition | `prop:kernel` (line 657) | The kernel dichotomy |
| Theorem | `thm:exact` (line 695) | Exactly which values of $x$ occur |
| Lemma | `lem:positivesquare` (line 839) | Every canonically positive element is a square |
| Theorem | `thm:orderforced` (line 859) | Order is algebraically forced |
| Theorem | `thm:reversal` (line 904) | Exponent-reversing isomorphism |
| Theorem | `thm:classification` (line 972) | Complete existence criterion for pure monomial data |
| Proposition | `prop:rational` (line 1093) | Untitled |
| Proposition | `prop:algebraic` (line 1167) | Criterion for a simple algebraic extension |
| Lemma | `lem:subseq` (line 1412) | Nondecreasing subsequences |
| Lemma | `lem:higman` (line 1440) | Higman's lemma, well-ordered alphabet case |
| Lemma | `lem:neumann` (line 1479) | Positive-support summability |
| Corollary | `cor:convolution` (line 1524) | Untitled |
| Lemma | `lem:two-supports` (line 1553) | Two supports, elementarily |
| Corollary | `cor:substitution` (line 1575) | Substitution into a positive-support series |
| Proposition | `prop:field` (line 1605) | Untitled |
