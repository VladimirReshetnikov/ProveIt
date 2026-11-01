# Intuitionistic PRA proof-existence target

The active objective is a Lean proof that the chosen literal equation's
no-positive-solution sentence is equivalent to the chosen formal `Con(ZFC)`
sentence in **intuitionistic** primitive recursive arithmetic. This is a
proof-existence statement, not a request to print a proof and not a proof of
either side separately. No such iPRA endpoint is currently claimed.

The candidate [native object theory](Lean/DiophantineConsistency/IPRANativeTheory.lean)
uses the existing finite primitive-recursive function-code language, native
defining equations, successor and order axioms, intuitionistic Leibniz
equality and parameterized quantifier-free induction. Its guarded author and
independent suffix replays have passed. Identifying this
candidate with a standard intuitionistic PRA presentation and proving the
connection to the conclusion remain obligations. It is neither classical
`PRATheory.PRA` nor merely the negative translation of that theory. The
existing classical induction scheme advances by
the syntactic term `n + 1`, whereas the language also has a distinct successor
code; a comparison with successor-form induction must prove their equality.
Classical formulas use negation-normal syntax, so interpreting a classical
implication by first expanding it as `¬A ∨ B` would give a different, generally
stronger intuitionistic formula than `A → B`. In particular, the intended
induction axioms must be constructed with the intuitionistic implication
connective rather than obtained by an unchecked syntactic embedding of the
classical induction formula.

An existing reusable starting point is
[`FoundationTheoryGG.theory_intuitionistic`](Lean/DiophantineConsistency/FoundationTheoryGG.lean),
which transforms a classical proof over any suitable language into an
intuitionistic proof of its Gödel–Gentzen translation over translated axioms.
The [expanded-language conditional bridge](Lean/DiophantineConsistency/IntuitionisticPRABridge.lean)
and its [literal 14-variable client](Lean/DiophantineConsistency/IntuitionisticPRACurrent.lean)
now have guarded author and independent replays over a verified prefix of the
equation build. They keep the classical derivation, all translated-axiom proofs and,
where applicable, the final target-comparison proof as explicit hypotheses.
They do not discharge those hypotheses or define native iPRA; the full
equation provider and external ancestry retain the limits in their
[replay packet](reviews/ipra-theory-transfer-prefix-replay/README.md).
The separately replayed [iff translation](Lean/DiophantineConsistency/IPRAIffGG.lean)
unpacks the translated classical comparison into a comparison of translated
sides. It does not identify the translated refutation side with ordinary
intuitionistic consistency.
The classical PRA source-current construction in
[PRA_PROVABILITY_PLAN.md](PRA_PROVABILITY_PLAN.md) can supply the starting
proof, but the following further steps are required in Lean:

1. Identify the defined native candidate with a standard intuitionistic PRA
   presentation, including its full primitive-recursive language and allowed
   induction parameters.
2. Revalidate the checked translated-axiom transfer after the merge and join
   it to the current equation proof. All classical PRA axiom images have been
   derived in the candidate; decidability and stability facts for the final
   consistency comparison remain separate.
3. Prove that the translated conclusion entails the intended literal
   intuitionistic equivalence, for both the no-zero formula and the selected
   arithmetized ZFC consistency predicate. It is not enough to identify these
   only in the standard model or to assume a generic conservation theorem.
4. Combine the resulting proof existence with coherent, source-authenticated
   equation and classical-PRA dependencies for each selected equation.

The focused [quantifier-free translation](Lean/DiophantineConsistency/IPRAQuantifierFree.lean)
establishes a useful syntactic special case: Gödel–Gentzen translation
preserves quantifier-freeness, commutes with finite universal closure, and
translates a classical negative equality to literal intuitionistic negated
equality. That does not require equality decidability. An author and an
independent strict suffix replay have passed; their parent and external
transitive ancestry are inherited as documented in the
[replay packet](reviews/ipra-quantifier-free-replay/README.md). This does not
address the arithmetized consistency predicate or the iPRA axiom images.
The separate [native induction syntax](Lean/DiophantineConsistency/IPRANativeInduction.lean)
uses intuitionistic implication and the exact `n + 1` term; it and the
[mapped no-zero identity](Lean/DiophantineConsistency/IPRAMappedNoZero.lean)
have also passed author and independent suffix replays. The native schema is
not yet a complete iPRA theory, and eligibility of translated matrices is
not a derivation of translated classical induction axioms.
The first native axiom-image result,
[successor nonzero](Lean/DiophantineConsistency/IPRANativeAxiomImage.lean),
has author and independent suffix replays. All five primitive-recursive
[defining-equation images](Lean/DiophantineConsistency/IPRANativeEquationImages.lean)
have also passed author and independent suffix replays; these do not discharge
the equality images. The separate
[basic-axiom images](Lean/DiophantineConsistency/IPRANativeBasicImages.lean)
now cover all three basic axioms and have passed author and independent
suffix replays. Equality reflexivity, symmetry, transitivity, arbitrary-arity
function congruence, and relation congruence have now all been translated.
The independently degree-certified 13-variable, 87-operation candidate
has [preliminary classical and native clients](reviews/pra87-translated-preliminary/README.md)
that compiled on an audited surviving-object overlay. A subsequent guarded
[38-module author and independent replays](reviews/ipra87-bundle-followup-translated-join-independent-pass/README.md)
have passed with matching rows on the classical bundle snapshot. Later source
refresh, inherited provider ancestry, and ordinary native consistency comparison
remain open; the native theorem concerns translated refutation.

The [13-variable native translated-refutation client](Lean/DiophantineConsistency/IPRA86TranslatedRefutation.lean)
has also compiled in a [preliminary provider union](reviews/ipra86-translated-refutation-preliminary/README.md)
with no additional theorem hypothesis. That union has a recorded partial
object audit but the original 86-side compile environment was not fully
reauthenticated. Subsequent [35-module guarded author and independent replays](reviews/ipra86-bundle-followup-translated-join-independent-pass/README.md)
have passed with matching rows on the authenticated classical bundle snapshot.
Later source refresh and ordinary native consistency comparison remain open.

The exact 14-variable client in
[IPRACurrentTranslatedRefutation.lean](Lean/DiophantineConsistency/IPRACurrentTranslatedRefutation.lean)
now has matching guarded author and independent replays on the explicitly
historical source snapshot, and matching author/independent bundle-followup
replays have since passed. It proves native-theory equivalence of its literal
no-zero sentence with negation of the GG-translated Foundation refutation
predicate. The comparison with the intended ordinary native consistency
sentence and a current-source replay remain separate obligations.

The [complete GG transfer](Lean/DiophantineConsistency/IPRAFullGGTransfer.lean)
combines every classical PRA axiom image and has matching guarded suffix
replays on source/object-matched historical parents. This proves that a
classical candidate-PRA proof translates to a proof of its GG image in the
native candidate; it does not identify ordinary intuitionistic consistency
with that translated image, and the post-merge source closure remains to be
revalidated.
The [translated induction body](Lean/DiophantineConsistency/IPRAInductionGGBody.lean)
has author and independent suffix replays: it proves intuitionistically that
the GG image of Foundation's exact `succInd` body is equivalent to the
implication-shaped induction body for the translated matrix. Closing its
free parameters has also passed author and independent suffix replays in
[IPRAInductionGGClosure.lean](Lean/DiophantineConsistency/IPRAInductionGGClosure.lean),
including the exact Foundation `univCl'` form. Identifying that closed body
with the native finite-parameter schema and deriving the full axiom from it
remain to be checked.
The [finite-matrix construction](Lean/DiophantineConsistency/IPRAInductionFiniteMatrix.lean)
has also passed author and independent suffix replays. It constructs an open,
finite-parameter matrix from each actual Foundation open induction matrix and
proves that its translated induction instance belongs to the native schema;
it does not yet identify that instance with the exact closed Foundation body.
The later [induction-axiom transfer](Lean/DiophantineConsistency/IPRAInductionAxiomGG.lean)
completes that identification: for an intuitionistic theory containing the
native induction schema, it derives the GG image of every actual Foundation
open-induction axiom. Author and independent suffix replays passed; comparison
of their hashes and the inherited external ancestry are recorded separately.
The other PRA axiom families still require their own translations.
The [native-theory specialization](Lean/DiophantineConsistency/IPRAInductionNativeGG.lean)
has also passed author and independent coherent suffix replays: it removes the
schema-inclusion premise for the candidate `nativeTheory` itself.

The chosen refutation sentence `rho` is the actual Foundation
`provabilityPred ZFC ⊥`, and its source consistency sentence is definitionally
`¬rho`. Although `rho` has a checked Σ₁ hierarchy certificate, its displayed
definition is not simply a visibly bounded matrix. The existing classical
PRA proof of `rho → ∃ b, bnd rho b` uses classical model completeness; it is
not an intuitionistic PRA proof. Its Gödel–Gentzen translation is now
constructed in [IPRAZFCRefutationBoundGG.lean](Lean/DiophantineConsistency/IPRAZFCRefutationBoundGG.lean):
the source-directed author and independent replays passed for the exact Foundation
ZFC refutation predicate, with matching source, object and full-log rows. This
gives the translated implication, not an unnegated intuitionistic witness.
After the witness-calculus merge, a [58-module source-directed rebuild](reviews/ipra-zfc-bound-postmerge-replay/README.md)
passed matching author and independent replays against the frozen historical
parent. Its recorded project and external ancestry is still inherited. A later
upstream refactor changed the bound endpoint and made `PRAConBForward` relevant;
a [six-module certificate refresh](reviews/ipra-zfc-bound-certificate-replay/README.md)
has now passed matching author and independent replays, with the inherited
ancestry boundary stated there. A later [historical single-provider join](Lean/DiophantineConsistency/IPRADeepBoundJoin.lean)
has independently replayed the translated bound together with the exact ZFC
deep-stability client, discharging its bound premise. Its native equality
decision and remaining deep-matrix stability proofs remain explicit; the
inherited ancestry and current-source limitations are recorded in its receipt.
The analogous HA normalization also uses
bounded decisions and finite double-negation shifts derived with HA
induction. A possible iPRA route is to construct primitive-recursive
decision codes for the particular bounded matrices and prove the necessary
bounding and translation statements with quantifier-free induction, but
those intuitionistic derivations remain open.

For open classical NNF formulas, [IPRAOpenAtomDecision.lean](Lean/DiophantineConsistency/IPRAOpenAtomDecision.lean)
constructs native decidability and the implication from the GG translation to
the native formula when proofs deciding its actual atoms are supplied. The
matched [author](reviews/ipra-open-atom-decision-author.md) and
[independent](reviews/ipra-open-atom-decision-independent.md) replays retain a
historical provider boundary. This does not itself supply those atom decisions
or treat bounded quantifiers. A [zero-atom specialization](Lean/DiophantineConsistency/IPRAZeroAtomDecision.lean)
handles every open NNF formula built from equalities or inequalities between
arbitrary terms and zero, assuming an explicit native zero-decidability proof;
its author and independent replays match on a historical provider.
A separately replayed [subtraction implication](Lean/DiophantineConsistency/IPRASubSuccZeroNative.lean)
proves `(Sx − y = 0) → (x − y = 0)` in the native theory without an extra
arithmetic premise. A second matched replay proves
`(u − S(v) = 0) → pred(u − v) = 0` natively; see
[IPRASubPredZeroNative.lean](Lean/DiophantineConsistency/IPRASubPredZeroNative.lean).
The native theory now proves **universal equality decidability** without an
extra arithmetic premise. [IPRANativeEqualityDecidable.lean](Lean/DiophantineConsistency/IPRANativeEqualityDecidable.lean)
constructs the proof object; its guarded author and independent replays match.
The project, Foundation and package ancestry of the selected provider remains
historical. On that provider, [IPRANativeOpenDecidable.lean](Lean/DiophantineConsistency/IPRANativeOpenDecidable.lean)
constructs free-variable decisions for all open NNF formulas and order atoms,
and open-formula stability, with no extra proof premise. Its author and
independent replays match; it does not establish bounded-search stability.
A [native selector certificate](Lean/DiophantineConsistency/IPRABoundedSelector.lean)
now proves, for each primitive-recursive test code, that any zero witness
below a bound makes the fixed search output a zero witness below that bound.
It transfers a classical open certificate using native open-formula stability;
matched guarded replays retain the inherited provider boundary. Bounded
existential stability and characteristic correctness for the actual ZFC
matrix remain separate obligations. A [generic selector-stability client](Lean/DiophantineConsistency/IPRASelectorStability.lean)
proves existential stability from explicit selector, selected-instance
stability, and characteristic-correctness proofs; its guarded replays match.
A [checked open-characteristic client](Lean/DiophantineConsistency/IPRASelectorOpenCharacteristic.lean)
now discharges selected-instance stability using native open decision, while
retaining fresh-witness forward correctness, the selector implication and
selected-instance reverse correctness as explicit premises. Binding those
the characteristic-correctness premises to the actual bounded matrix remains
to be checked. The [concrete search binding](Lean/DiophantineConsistency/IPRASelectorSearchBinding.lean)
now supplies the selector implication from the actual `searchCode`, leaving
only the two pointwise characteristic-correctness directions explicit; its
matched guarded replays retain historical ancestry.

The construction proves the open-induction invariant
`x−y≠0 ∨ (y−x≠0 ∨ x=y)`. Its [base case](Lean/DiophantineConsistency/IPRADifferenceInvariantBase.lean)
is checked, and its successor case uses the native positive
[subtraction reconstruction](Lean/DiophantineConsistency/IPRAReconstructClosure.lean)
`y−x=0 ∨ x+(y−x)=y`. The resulting
[successor bridge](Lean/DiophantineConsistency/IPRAReconstructBridge.lean)
`y−Sx=0 → (y−x≠0 → Sx=y)` and its open-term family are rebuilt on the same
provider as the quantified induction step. The [forward difference theorem](Lean/DiophantineConsistency/IPRANativeDifferenceForward.lean)
was similarly joined with native zero decidability. The intermediate modules
retain their stated explicit premises; the equality endpoint discharges them.

The native positive addition identities `x+0=x` and `x+S(y)=S(x+y)` have
also been checked by [direct defining-equation proofs](Lean/DiophantineConsistency/IPRAAddRecursion.lean),
with matching author and independent replays. The companion
[successor-left identity](Lean/DiophantineConsistency/IPRASuccLeft.lean)
`S(x)+y=S(x+y)` is also checked natively with parameterized open induction.
The analogous direct native
[subtraction equations](Lean/DiophantineConsistency/IPRASubArithmetic.lean)
`x−0=x`, `x−S(y)=pred(x−y)`, and `pred(0)=0` have also passed matching
replays; these are positive equalities, not merely their GG images.

The theory now proves zero decidability without an additional premise. The
[checked native proof](Lean/DiophantineConsistency/IPRAZeroStepNative.lean)
translates the classical PRA proof of `x + 1 = S(x)` to obtain its
intuitionistic double negation; native Leibniz equality and successor
nonzeroness then prove `x + 1 ≠ 0` without eliminating the double negation.
Native open induction yields `∀ x, x = 0 ∨ ¬(x = 0)`. The author and
independent [guarded replays](reviews/ipra-zero-decidable-native-replay/README.md)
match, retaining the historical parent-object and external-ancestry boundary
stated there. This is only equality with zero: general equality, order and
bounded-formula decidability remain open. Independently, the ordinary positive
`∀x, x + 1 = S(x)` has now been proved directly from native defining equations
and Leibniz equality in [IPRAAddOneDirect.lean](Lean/DiophantineConsistency/IPRAAddOneDirect.lean),
with matching [guarded replays](reviews/ipra-addone-direct-replay/README.md).
This proof has no object-theory decidability premise. The native theory also
proves `∀x (x = 0 ∨ x = S(pred x))` by quantifier-free induction; see
[IPRAPredReconstruct.lean](Lean/DiophantineConsistency/IPRAPredReconstruct.lean)
and its [matched replays](reviews/ipra-pred-reconstruct-replay/README.md).
A separate [sub-self derivation](Lean/DiophantineConsistency/IPRANativeSubSelf.lean)
proves `∀x, x − x = 0` from an explicit zero-decidability proof by translating
the classical theorem and eliminating double negation only for equality with
zero; its author and independent replays match. The eventual composition with
the unconditional zero-decidability provider still requires an authenticated
join of their historical dependencies.
A fixed-parameter induction on one
argument cannot simply invoke its induction hypothesis at a changed parameter;
the corresponding quantified induction matrix is not quantifier-free.

It may suffice to translate the existing *classical* witness-bound proof,
instead of deriving an intuitionistic unnegated witness bound. If iPRA can
identify the translated bounded matrix with its ordinary interpretation up
to the needed double negation, and prove that an ordinary bounded witness
implies `rho`, the translated bound can potentially yield `rhoᴺ → ¬¬rho`.
Together with the other implication and the intuitionistic
`Derivation.neg_doubleNegation` lemma, this would compare the two consistency
sentences without extracting a witness from a double negation. This is a proof
plan, not yet a checked iPRA theorem.
The pure logical final step has an independently replayed proof-producing
lemma in [IPRARefutationNegationLogic.lean](Lean/DiophantineConsistency/IPRARefutationNegationLogic.lean):
it assumes proofs of `ordinary → rhoᴺ` and `rhoᴺ → ¬¬ordinary` and derives
the equivalence of `(¬rho)ᴺ` with `¬ordinary`. Its
[theory-context extension](Lean/DiophantineConsistency/IPRARefutationNegationTheory.lean)
has also passed author and independent replays, allowing both premises to be
proved in an arbitrary intuitionistic theory. The first premise, from a native
interpretation of a classical negation-normal formula to its GG translation,
is now proved generically in
[IPRANativeForwardTheory.lean](Lean/DiophantineConsistency/IPRANativeForwardTheory.lean)
and has author and independent guarded replays. Establishing the reverse
double-negated implication for the actual refutation predicate in the intended
iPRA remains open.
For the literal Foundation ZFC source sentence, the separately guarded
[one-premise client](Lean/DiophantineConsistency/IPRAFoundationZFCNegationOnePremise.lean)
now proves the desired consistency comparison for any intuitionistic theory
from the explicit backward double-negation premise. Author and independent
suffix replays passed, with the inherited HA/ZF/Foundation/package boundary
recorded in their receipts; the arithmetic premise is not yet proved.
The [language-mapped client](Lean/DiophantineConsistency/IPRAFoundationZFCMappedNegation.lean)
and a generic [witness-bound logic bridge](Lean/DiophantineConsistency/IPRARefutationWitnessBridge.lean)
have also passed author and independent suffix replays. The latter keeps all
three implications about a proposed bound as explicit premises; it neither
supplies those proofs nor yet identifies the bound with the literal ZFC one.
The [literal-bound specialization](Lean/DiophantineConsistency/IPRAFoundationZFCWitnessBound.lean)
now chooses exactly `∃ b, bnd rho` and has passed both author and independent
suffix replays, retaining all three implication premises. It also checks the
bounded-matrix hierarchy certificate. Those premises and the larger proof
chain have not thereby been established in iPRA.
The separately replayed [structural erasure](Lean/DiophantineConsistency/IPRABoundedErasure.lean)
proves the native bounded body implies the native unbounded body for closed
arithmetic NNF semisentences under term valuations, using intuitionistic
logic alone. The [outer-existential erasure](Lean/DiophantineConsistency/IPRABoundedExistsErasure.lean)
has also passed author and independent suffix replays in the arithmetic
language. Mapping that result to the PR language for the exact `rho`, and
identifying the translated bounded matrix with its ordinary interpretation,
remain separate obligations.

The repository's HA transfers and existing equation-side HA endpoints may
provide proof-system and negative-translation lemmas. HA has stronger
induction, so an HA proof alone does not establish an iPRA proof. Likewise,
Lean's classical metatheory for proving existence of a derivation is distinct
from adding classical logic to the object theory.

## Additional characteristic-code route

The [historical upstream plan](research/ipra-upstream-plan-20261031.md)
proposes reusing the classical bounded characteristic and search theorems by
negative translation, then recovering a native bounded-matrix comparison
using intuitionistic decidability. This is a possible route, not a checked
replacement for those constructive obligations: the translated bit equations,
bounded-search correctness, and quantifier cases must all be justified in
native iPRA. Its direct negation-normal reading of `succInd` must not be used
as native induction, for the implication reason explained above.
