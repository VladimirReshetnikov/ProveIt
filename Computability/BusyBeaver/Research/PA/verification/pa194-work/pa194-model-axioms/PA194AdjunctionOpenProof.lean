import PA194AdjunctionSourceSyntax
import PA194CongruenceSourceProof
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
namespace PA194AdjunctionOpenProof
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
open PA194FullSepOpen PA194TypedSeparation PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof



noncomputable def weakAdjunctionProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜weakAdjunctionFormula⌝ : Formula M SourceL) := by
  have hσ : sourceWeakAdjunction ∈ adjunctiveFullSepTheory := by
    change sourceWeakAdjunction ∈ adjunctiveTheory ∪ fullSepTheory
    left
    simp [adjunctiveTheory, adjunctiveList]
  have h := standardAxiomProof (M := M) sourceWeakAdjunction hσ
  rw [weak_adjunction_syntax] at h
  exact h

noncomputable def swappedSeparationProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜ND.separationAll (.fvar 1 : ND.Term) (.fvar 0 : ND.Term)⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  rw [swapped_separation]
  apply proofOfInternalProvable T (⌜separationFormula swappedAdjunctionProperty⌝ : Formula M SourceL)
  have h := adjunctive_full_sep_root_provable (⌜swappedAdjunctionProperty⌝ : M)
    (Semiformula.quote_isSemiformul₁ swappedAdjunctionProperty)
  rw [← separationFormula_quote] at h
  exact h

noncomputable def swappedAdjunctionOpenProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜ND.adjunctionExists (.fvar 1 : ND.Term) (.fvar 0 : ND.Term)⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T (ND.adjunctionAxioms (.fvar 1) (.fvar 0))
    (ND.adjunctionExists (.fvar 1 : ND.Term) (.fvar 0 : ND.Term)) swappedAdjunctionDerivation
  intro q hq
  by_cases h0 : q = weakAdjunctionFormula
  · subst q; exact weakAdjunctionProof
  by_cases h1 : q = ND.separationAll (.fvar 1 : ND.Term) (.fvar 0 : ND.Term)
  · subst q; exact swappedSeparationProof
  by_cases h2 : q = reflexivityFormula
  · subst q; exact reflexivityProof
  by_cases h3 : q = symmetryFormula
  · subst q; exact symmetryProof
  have h4 : q = congruenceFormula := by simpa [ND.adjunctionAxioms, h0, h1, h2, h3] using hq
  subst q
  exact congruenceProof

#print axioms weakAdjunctionProof
#print axioms swappedSeparationProof
#print axioms swappedAdjunctionOpenProof
end models
end PA194AdjunctionOpenProof
