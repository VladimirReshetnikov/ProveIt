import PA194OrdinalClosed
import PA194AdjunctionOpenProof
import PA194AdjunctionClosureTyped
import PA194CloseProof
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
namespace PA194StandardOrdinalProof
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
open PA194AdjunctionOpenProof PA194TypedClosure PA194IntersectionMember PA194CloseProof PA194OrdinalClosed




noncomputable def provableOfProof (T : InternalTheory M SourceL) (q : Formula M SourceL)
    (d : T ⊢! q) : Provable T.theory q.val := TProvable.iff_provable.mp ⟨d⟩

noncomputable def adjunctionProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜adjunctionFormula⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  let body : Proposition M6.PA.RelationalSource.language := ND.adjunctionExists (.fvar 1 : ND.Term) (.fvar 0 : ND.Term)
  have hp : IsSemiformula SourceL 0 (⌜body⌝ : M) := Semiformula.quote_isSemiformula₀ body
  have ho : Provable T.theory (⌜body⌝ : M) :=
    provableOfProof T (⌜body⌝ : Formula M SourceL) swappedAdjunctionOpenProof
  have hc := close_iterated_provable T ((2 : Nat) : M) (⌜body⌝ : M) hp ho
  have hf : body.fvSup = 2 := by decide
  have hclose : modelClose ((2 : Nat) : M) (⌜body⌝ : M) = (⌜body.univCl⌝ : M) := by
    simpa [hf] using modelClose_quote_univCl (M := M) body
  have htyped : (⌜body.univCl⌝ : M) = (⌜adjunctionFormula.univCl⌝ : M) :=
    congrArg (fun q : Sentence M6.PA.RelationalSource.language => (⌜q⌝ : M)) swapped_adjunction_closure
  have hq : (⌜adjunctionFormula.univCl⌝ : M) = (⌜adjunctionFormula⌝ : M) :=
    quote_univCl_eq_self adjunctionFormula (by decide)
  have ht : Provable T.theory (⌜adjunctionFormula⌝ : M) := by
    rw [hclose, htyped, hq] at hc
    exact hc
  exact proofOfInternalProvable T (⌜adjunctionFormula⌝ : Formula M SourceL) ht

noncomputable def standardOrdinalProof
    (p : Semiproposition M6.PA.RelationalSource.language 1) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜inductionStatement p⌝ : Formula M SourceL) :=
  standardOrdinalProofOfOne p adjunctionProof

theorem standard_closed_ordinal_provable
    (p : Semiproposition M6.PA.RelationalSource.language 1) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory (closedOrdinalInductionCode (⌜p⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  have hopen : Provable T.theory (⌜inductionStatement p⌝ : M) :=
    provableOfProof T (⌜inductionStatement p⌝ : Formula M SourceL) (standardOrdinalProof p)
  rw [← ordinalInductionCode_quote] at hopen
  exact close_iterated_provable T _ _ (ordinalInductionCode_scoped _ (Semiformula.quote_isSemiformul₁ p)) hopen

#print axioms standard_closed_ordinal_provable
#print axioms provableOfProof
#print axioms adjunctionProof
#print axioms standardOrdinalProof
end models
end PA194StandardOrdinalProof
