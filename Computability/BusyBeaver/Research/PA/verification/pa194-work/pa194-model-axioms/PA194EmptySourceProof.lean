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
namespace PA194EmptySourceProof
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
open PA194FullSepOpen PA194TypedSeparation PA194StandardEqualitySuppliers

def emptyFoundationDerivation : LO.FirstOrder.Derivation
    ([separationFormula (⊥ : Semiproposition M6.PA.RelationalSource.language 1)].map Semiformula.neg ++ [emptyFormula]) :=
  emptyFromFalseSeparation.contra (by simp [ND.Proof])

noncomputable def emptyProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜emptyFormula⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T [separationFormula (⊥ : Semiproposition M6.PA.RelationalSource.language 1)] emptyFormula emptyFoundationDerivation
  intro q hq
  have he : q = separationFormula (⊥ : Semiproposition M6.PA.RelationalSource.language 1) := by simpa using hq
  subst q
  apply proofOfInternalProvable T (⌜separationFormula (⊥ : Semiproposition M6.PA.RelationalSource.language 1)⌝ : Formula M SourceL)
  have h := adjunctive_full_sep_root_provable (⌜(⊥ : Semiproposition M6.PA.RelationalSource.language 1)⌝ : M)
    (Semiformula.quote_isSemiformul₁ _)
  rw [← separationFormula_quote] at h
  exact h

noncomputable def standardOrdinalProofOfTwo
    (p : Semiproposition M6.PA.RelationalSource.language 1)
    (adjunctionProof : let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
      T ⊢! (⌜adjunctionFormula⌝ : Formula M SourceL))
    (congruenceProof : let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
      T ⊢! (⌜congruenceFormula⌝ : Formula M SourceL)) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜inductionStatement p⌝ : Formula M SourceL) :=
  standardOrdinalProofOfThree p emptyProof adjunctionProof congruenceProof

#print axioms standardOrdinalProofOfTwo
#print axioms emptyFoundationDerivation
#print axioms emptyProof
end models
end PA194EmptySourceProof
