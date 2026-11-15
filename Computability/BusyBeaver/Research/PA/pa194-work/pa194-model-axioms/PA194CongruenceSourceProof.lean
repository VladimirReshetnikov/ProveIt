import PA194CongruenceFromRelExt
import PA194EmptySourceProof
import PA194StandardEqualitySuppliers
import PA194EmptyFromSep
import PA194StandardOrdinalReduction
import PA194OrdinalSuppliers
import PA194FoundationOrdinalInductionNumeric
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
import PA194InternalOrdinalStatement
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194CongruenceSourceProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194StandardOrdinalReduction PA194QuotedInduction PA194OrdinalSuppliers PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
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

open M6.PA.RelationalSource
open M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.ND
open PA194FullSepOpen PA194TypedSeparation PA194StandardEqualitySuppliers PA194EmptySourceProof


def congruenceFoundationDerivation : LO.FirstOrder.Derivation
    ([relExtForm].map Semiformula.neg ++ [congruenceFormula]) :=
  congruenceFromRelExt.contra (by simp [ND.Proof])

noncomputable def congruenceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜congruenceFormula⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T [relExtForm] congruenceFormula congruenceFoundationDerivation
  intro q hq
  have he : q = relExtForm := by simpa using hq
  subst q
  have ha : PA194RelExtTypedTranslation.sourceRelExt ∈ adjunctiveFullSepTheory := by
    change PA194RelExtTypedTranslation.sourceRelExt ∈ adjunctiveTheory ∪ fullSepTheory
    left
    simp [adjunctiveTheory, adjunctiveList]
  have h := standardAxiomProof (M := M) PA194RelExtTypedTranslation.sourceRelExt ha
  rw [relExt_syntax] at h
  exact h

noncomputable def standardOrdinalProofOfOne
    (p : Semiproposition M6.PA.RelationalSource.language 1)
    (adjunctionProof : let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
      T ⊢! (⌜adjunctionFormula⌝ : Formula M SourceL)) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜inductionStatement p⌝ : Formula M SourceL) :=
  standardOrdinalProofOfTwo p adjunctionProof congruenceProof

#print axioms congruenceFoundationDerivation
#print axioms congruenceProof
#print axioms standardOrdinalProofOfOne
end models
end PA194CongruenceSourceProof
