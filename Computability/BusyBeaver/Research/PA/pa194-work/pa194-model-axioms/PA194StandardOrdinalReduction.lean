import PA194QuotedInduction
import PA194OrdinalSuppliers
import PA194FoundationOrdinalInductionNumeric
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
import PA194InternalOrdinalStatement
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194StandardOrdinalReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194QuotedInduction PA194OrdinalSuppliers PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
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
local instance freeBoundClosedLeafZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundClosedLeafOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundClosedLeafAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundClosedLeafMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundClosedLeafLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundClosedLeafIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open M6.PA.RelationalSource
open M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

noncomputable def proofOfInternalProvable (T : InternalTheory M SourceL)
    (q : Formula M SourceL) (h : Provable T.theory q.val) : T ⊢! q :=
  ((TProvable.iff_provable).2 h).get

/-- The negated-property separation and intersection premises are supplied;
only the six formulas of exactContext remain assumptions. -/
noncomputable def standardOrdinalProofOfExactContext
    (p : Semiproposition M6.PA.RelationalSource.language 1)
    (h : let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
      ∀ q ∈ exactContext, T ⊢! (⌜q⌝ : Formula M SourceL)) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜inductionStatement p⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  apply standardOrdinalProof T p
  intro q hq
  by_cases hx : q ∈ exactContext
  · exact h q hx
  by_cases hi : q = intersectionFormula
  · subst q
    apply proofOfInternalProvable T (⌜intersectionFormula⌝ : Formula M SourceL)
    exact PA194IntersectionMember.intersection_provable
  have hs : q = separationFormula (∼p) := by
    simpa [inductionContext, hx, hi] using hq
  subst q
  apply proofOfInternalProvable T (⌜separationFormula (∼p)⌝ : Formula M SourceL)
  exact typed_negated_property_separation_provable p

#print axioms standardOrdinalProofOfExactContext
end models
end PA194StandardOrdinalReduction
