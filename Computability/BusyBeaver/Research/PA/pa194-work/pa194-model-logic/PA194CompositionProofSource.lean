import PA194CompositionContext
import PA194CompositionSource
import PA194ForwardMulZeroSource
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194CompositionSymmetrySource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194EmptySourceProof PA194StandardOrdinalProof PA194CompositionSource PA194CompositionContext PA194TypedSchema PA194CompositionClosedTemplate PA194StandardEqualitySuppliers PA194CongruenceSourceProof M6.PA.RelationalSource.PairGraph PA194BindSource PA194StandardOrdinalReduction PA194QuotedInduction PA194OrdinalSuppliers PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
open PA194OrdinalStatementFromProperty PA194OrdinalStepFromProperty PA194OrdinalBaseQuote PA194OrdinalConclusionQuote
  PA194InternalOrdinalBase PA194InternalOrdinalConclusion PA194OrdinalPropertyPlacement PA194OrdinalStepQuote
  PA194TypedSeparation PA194InternalOrdinalStep M6.PA.RelationalSource.Ordinal
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance compositionSymmetryLeafZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance compositionSymmetryLeafOne : One M := ⟨F oneCode Fin.elim0⟩
local instance compositionSymmetryLeafAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance compositionSymmetryLeafMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance compositionSymmetryLeafLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance compositionSymmetryLeafIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open M6.PA.RelationalSource
open M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

open PA194ModelLogic
open M6.PA.RelationalSource
noncomputable def compositionSourceProof (a b c : Nat) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜compositionStatement a b c⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T compositionAxioms (compositionStatement a b c)
    (compositionDerivation a b c)
  intro q hq
  by_cases h0 : q = closedCompositionSeparation
  · subst q; exact closedCompositionSeparationProof
  by_cases h1 : q = reflexivityFormula
  · subst q; exact reflexivityProof
  by_cases h2 : q = symmetryFormula
  · subst q; exact symmetryProof
  by_cases h3 : q = congruenceFormula
  · subst q; exact congruenceProof
  by_cases h4 : q = transitivityFormula
  · subst q; exact transitivityProof
  by_cases h5 : q = emptyFormula
  · subst q; exact emptyProof
  by_cases h6 : q = adjunctionFormula
  · subst q; exact adjunctionProof
  have h7 : q = Ordinal.intersectionFormula := by
    simpa [compositionAxioms,h0,h1,h2,h3,h4,h5,h6] using hq
  subst q
  apply proofOfInternalProvable T (⌜Ordinal.intersectionFormula⌝ : Formula M SourceL)
  exact PA194IntersectionMember.intersection_provable
#print axioms compositionSourceProof
end models
end PA194CompositionSymmetrySource
